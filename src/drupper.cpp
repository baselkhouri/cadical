#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Enable proof drupping.

void Internal::drup () {
  assert (!drupper);
  drupper = new Drupper (this);
}

void Internal::trim (ClauseIterator &it) {
  assert (drupper);
  drupper->trim (it);
}

/*------------------------------------------------------------------------*/

struct CoreVerifier : public ClauseIterator {
  Solver s;
  CoreVerifier () {
    s.set ("drup", 0);
    s.set ("stats", 0);
    s.set ("report", false);
  }
  bool clause (const std::vector<int> &c) {
    for (int lit : c)
      s.add (lit);
    s.add (0);
    return true;
  }
  bool verified () {
    assert (!s.status ());
    return s.solve () == 20;
  }
};

struct CorePrinter : public ClauseIterator {
  File *file;
  CorePrinter (Internal *i, const char *path, int vars, int clauses) {
    file = File::write (i, path);
    file->put ("p cnf ");
    file->put (vars);
    file->put (" ");
    file->put (clauses);
    file->put ('\n');
  }

  ~CorePrinter () { delete file; }

  bool clause (const std::vector<int> &c) {
    for (int lit : c)
      file->put (lit), file->put (' ');
    file->put ("0\n");
    return true;
  }
};

/*------------------------------------------------------------------------*/

DrupperClause::DrupperClause (vector<int> c, bool deletion)
    : deleted (deletion), revive_at (0) {
  assert (c.size ());
  variant = LITERALS;
  literals = new std::vector<int> (c);
};

DrupperClause::DrupperClause (Clause *c, bool deletion)
    : deleted (deletion), revive_at (0) {
  assert (c && c->size);
  variant = CLAUSE;
  counterpart = c;
};

DrupperClause::~DrupperClause () { destroy_variant (); }

DCVariant DrupperClause::variant_type () const {
  return variant ? LITERALS : CLAUSE;
}

void DrupperClause::destroy_variant () {
  if (variant_type () == CLAUSE)
    counterpart = 0;
  else
    delete literals;
}

void DrupperClause::set_variant (Clause *c) {
  destroy_variant ();
  variant = CLAUSE;
  counterpart = c;
}

void DrupperClause::set_variant (const vector<int> &c) {
  destroy_variant ();
  variant = LITERALS;
  literals = new std::vector<int> (c);
}

Clause *DrupperClause::flip_variant () {
  assert (variant_type () == CLAUSE);
  Clause *ref = counterpart;
  assert (ref);
  set_variant (vector<int> ());
  for (int lit : *ref)
    literals->push_back (lit);
  return ref;
}

Clause *DrupperClause::clause () {
  assert (variant_type () == CLAUSE);
  return counterpart;
}

vector<int> &DrupperClause::lits () {
  assert (variant_type () == LITERALS && literals);
  return *literals;
}

const vector<int> &DrupperClause::lits () const {
  assert (variant_type () == LITERALS && literals);
  return *literals;
}

/*------------------------------------------------------------------------*/

Drupper::Drupper (Internal *i)
    : internal (i), failed_constraint (0), final_conflict (0), isolated (0),
      in_action (0), overconstrained (0) {
  LOG ("DRUPPER new");

  setup_internal_options ();
}

Drupper::~Drupper () {
  LOG ("DRUPPER delete");
  isolated = true;
  for (const auto &dc : proof)
    delete (DrupperClause *) dc;
  for (const auto &c : unit_clauses)
    delete[](char *) c;
}
/*------------------------------------------------------------------------*/

void Drupper::set (const char *setting, bool val) {
  if (!strcmp (setting, "core_units"))
    settings.core_units = val;
  else if (!strcmp (setting, "incremental"))
    settings.incremental = val;
  else if (!strcmp (setting, "check_core"))
    settings.check_core = val;
  else
    assert (0 && "unknown drupper seting");
}

bool Drupper::setup_internal_options () {
  auto &opts = internal->opts;
  bool updated = false;
  updated |= opts.chrono;
  updated |= opts.probe;
  updated |= opts.compact;
  updated |= opts.checkproof;
  opts.chrono = 0;
  opts.probe = 0;
  opts.compact = 0;
  opts.checkproof = 0;
  return updated;
}

/*------------------------------------------------------------------------*/

Clause *Drupper::new_redundant_clause (const vector<int> &clause) {

  assert (clause.size () <= (size_t) INT_MAX);
  const int size = (int) clause.size ();
  assert (size >= 2);

  size_t bytes = Clause::bytes (size);
  Clause *c = (Clause *) new char[bytes];

  c->conditioned = false;
  c->covered = false;
  c->enqueued = false;
  c->frozen = false;
  c->garbage = false;
  c->gate = false;
  c->hyper = false;
  c->instantiated = false;
  c->keep = false;
  c->moved = false;
  c->reason = false;
  c->redundant = true;
  c->transred = false;
  c->subsume = false;
  c->vivified = false;
  c->vivify = false;
  c->used = 0;

  c->glue = 0;
  c->size = size;
  c->pos = 2;

  for (int i = 0; i < size; i++)
    c->literals[i] = clause[i];

  assert (c->bytes () == bytes);
  auto &istats = internal->stats;
  istats.current.total++;
  istats.added.total++;
  istats.current.redundant++;
  istats.added.redundant++;

  internal->clauses.push_back (c);
  return c;
}

void Drupper::mark_garbage (Clause *c) {
  assert (c);
  if (c->garbage)
    return;
  c->garbage = true;
  if (c->size == 1)
    return;
  size_t bytes = c->bytes ();
  auto &istats = internal->stats;
  assert (istats.current.total > 0);
  istats.current.total--;
  if (c->redundant) {
    assert (istats.current.redundant > 0);
    istats.current.redundant--;
  } else {
    assert (istats.current.irredundant > 0);
    istats.current.irredundant--;
    assert (istats.irrlits >= c->size);
    istats.irrlits -= c->size;
  }
  istats.garbage.bytes += bytes;
  istats.garbage.clauses++;
  istats.garbage.literals += c->size;
  c->used = 0;
}

void Drupper::mark_active (Clause *c) {
  assert (c);
  if (!c->garbage)
    return;
  c->garbage = false;
  if (c->size == 1)
    return;
  size_t bytes = c->bytes ();
  auto &istats = internal->stats;
  istats.current.total++;
  if (c->redundant) {
    istats.current.redundant++;
  } else {
    istats.current.irredundant++;
    istats.irrlits += c->size;
  }
  assert (istats.garbage.bytes >= bytes);
  istats.garbage.bytes -= bytes;
  assert (istats.garbage.clauses > 0);
  istats.garbage.clauses--;
  assert (istats.garbage.literals > 0);
  istats.garbage.literals -= c->size;
}

Clause *Drupper::new_unit_clause (int lit, bool original) {

  size_t bytes = Clause::bytes (1);
  Clause *c = (Clause *) new char[bytes];

  stats.units++;

  c->conditioned = false;
  c->covered = false;
  c->enqueued = false;
  c->frozen = false;
  c->garbage = false;
  c->gate = false;
  c->hyper = false;
  c->instantiated = false;
  c->keep = true;
  c->moved = false;
  c->reason = false;
  c->redundant = !original;
  c->transred = false;
  c->subsume = false;
  c->vivified = false;
  c->vivify = false;
  drup_db[c].lemma = !original;
  c->used = c->glue = 0;
  c->size = 1;
  c->pos = 2;
  c->literals[0] = lit;

  assert (c->bytes () == bytes);

  unit_clauses.push_back (c);
  LOG (c, "new pointer %p", (void *) c);

  return c;
}

/*------------------------------------------------------------------------*/

void Drupper::append_lemma (DrupperClause *dc) {
  assert (proof.size () <= (1u << 30) - 1 &&
          "Possible overflow in revive_at/drup.idx members!");
  if (dc->deleted)
    stats.deleted++;
  else
    stats.derived++;
  if (dc->variant_type () == CLAUSE) {
    Clause *c = dc->clause ();
    auto &c_drup = drup_db[c];
    if (c_drup.idx && dc->deleted) {
      assert (proof[c_drup.idx - 1]->clause () == c);
      dc->revive_at = c_drup.idx;
    }
#ifndef NDEBUG
    // Ensure reason clauses are not deleted.
    int lit = c->literals[0];
    if (internal->fixed (lit) && internal->var (lit).reason == c)
      assert (!c->garbage);
#endif
    c_drup.idx = proof.size () + 1;
    assert (!core (c));
  }
  proof.push_back (dc);
}

void Drupper::append_failed (const vector<int> &c) {
  append_lemma (new DrupperClause (c));
  append_lemma (new DrupperClause (c, true));
  int i = proof.size () - 1;
  proof[i]->revive_at = i;
}

void Drupper::revive_clause (const int i) {
  assert (i >= 0 && i < proof.size ());
  DrupperClause *dc = proof[i];
  assert (dc->deleted);
  Clause *c = nullptr;
  if (dc->variant_type () == CLAUSE)
    c = dc->clause ();
  else {
    const auto &literals = dc->lits ();
    c = new_redundant_clause (literals);
    mark_garbage (c);
    drup_db[c].idx = i + 1;
    dc->set_variant (c);
  }
  assert (c && c->garbage);
  mark_active (c);
  // This is a hack to easily iderntify the irredundant core.
  // Every revived clause will be considered as an irredundant
  // lemma. If it's a redundant lemma, it will be marked as
  // redundant later in the the main trimming loop.
  drup_db[c].lemma = false;
  internal->watch_clause (c);
  for (int lit : *c)
    if (internal->flags (lit).eliminated ())
      internal->reactivate (lit);
  if (dc->revive_at) {
#ifndef NDEBUG
    int j = dc->revive_at - 1;
    assert (j < i && j >= 0);
    assert (!proof[j]->revive_at); // Are chains even possible?
    assert (!proof[j]->deleted);
#endif
    proof[dc->revive_at - 1]->set_variant (c);
  }
  stats.revived++;
}

void Drupper::stagnate_clause (Clause *c) {
  {
    // See the discussion in 'propagate' on avoiding to eagerly trace binary
    // clauses as deleted (produce 'd ...' lines) as soon they are marked
    // garbage.
    assert (!c->garbage && "remove this if you are actually delaying the "
                           "trace of garbage binaries");
  }
  assert (!c->moved);
  mark_garbage (c);
  /// TODO: Avoid calling unwatch_clause () and try flushing watches before
  /// propagating instead.
  if (c->size > 1)
    internal->unwatch_clause (c);
}

/// NOTE: The internal solver does not support reactivation
// of fixed literals. However, this is needed to be able
// to propagate these literals again.
void Drupper::reactivate_fixed (int l) {
  Flags &f = internal->flags (l);
  assert (f.status == Flags::FIXED);
  assert (internal->stats.now.fixed > 0);
  internal->stats.now.fixed--;
  f.status = Flags::ACTIVE;
  assert (internal->active (l));
  internal->stats.reactivated++;
  assert (internal->stats.inactive > 0);
  internal->stats.inactive--;
  internal->stats.active++;
}

/*------------------------------------------------------------------------*/

void Drupper::shrink_internal_trail (const unsigned trail_sz) {
  assert (trail_sz <= internal->trail.size ());
  internal->trail.resize (trail_sz);
  internal->propagated = trail_sz;
  /// TODO: set internal->propagated2 properly.
  assert (!internal->level);
  assert (internal->control.size () == 1);
}

void Drupper::clean_conflict () {
  internal->unsat = false;
  internal->backtrack ();
  internal->conflict = 0;
}

/*------------------------------------------------------------------------*/

void Drupper::undo_trail_literal (const int lit) {
  assert (internal->val (lit) > 0);
  if (!internal->active (lit))
    reactivate_fixed (lit);
  internal->unassign (lit);
  assert (!internal->val (lit));
  assert (internal->active (lit));
#ifndef NDEBUG
  Var &v = internal->var (lit);
  assert (v.reason);
  // v.reason = 0;
#endif
}

void Drupper::undo_trail_core (Clause *c, unsigned &trail_sz) {
#ifndef NDEBUG
  assert (trail_sz > 0);
  assert (trail_sz <= internal->trail.size ());
  assert (c && is_on_trail (c));
#endif

  int clit = c->literals[0];

#ifndef NDEBUG
  assert (internal->var (clit).reason == c);
  assert (internal->val (clit) > 0);
#endif

  while (internal->trail[--trail_sz] != clit) {
    assert (trail_sz > 0);
    int l = internal->trail[trail_sz];

    Clause *r = internal->var (l).reason;
    assert (r && r->literals[0] == l);

    undo_trail_literal (l);

    if (settings.core_units)
      mark_core (r);

    if (core (r))
      for (int j = 1; j < r->size; j++)
        mark_core (internal->var (r->literals[j]).reason);
  }

  assert (clit == internal->trail[trail_sz]);
  undo_trail_literal (clit);
}

bool Drupper::is_on_trail (Clause *c) const {
  assert (c);
  int lit = c->literals[0];
  return internal->val (lit) > 0 && internal->var (lit).reason == c;
}

/*------------------------------------------------------------------------*/

bool Drupper::lemma (Clause *c) const {
  assert (c);
  bool val = false;
  const auto it = drup_db.find(c);
  if (it != drup_db.end ())
    val = it->second.lemma;
  return val;
}

bool Drupper::core (Clause *c) const {
  assert (c);
  bool val = false;
  const auto it = drup_db.find(c);
  if (it != drup_db.end ())
    val = it->second.core;
  return val;
}

void Drupper::unmark_core (Clause *c) {
  assert (c);
  drup_db[c].core = false;
}

void Drupper::mark_core (Clause *c) {
  assert (c);
  drup_db[c].core = true;
}

void Drupper::mark_conflict_lit (const int l) {
  assert (internal->val (l) < 0);
  Var &v = internal->var (l);
  Clause *reason = v.reason;
  if (reason)
    mark_core (reason);
}

void Drupper::mark_conflict () {
  if (internal->unsat) {
    assert (final_conflict);
    mark_core (final_conflict);
    for (int lit : *final_conflict)
      mark_conflict_lit (lit);
  } else {
    // assert (!internal->marked_failed || failing_assumptions.size ());
    // assert (internal->marked_failed || failing_assumptions.empty ());
    if (internal->unsat_constraint && internal->constraint.size () > 1) {
      failed_constraint = new_redundant_clause (internal->constraint);
      mark_core (failed_constraint);
      internal->watch_clause (failed_constraint);
    }
    if (!internal->marked_failed) {
      internal->failing ();
      internal->marked_failed = true;
    }
  }
}

void Drupper::mark_failing (const int proof_sz) {
  assert (proof_sz < proof.size () && !((proof.size () - proof_sz) % 2));
  for (int i = proof_sz; i < proof.size (); i++)
    if ((i - proof_sz) % 2) {
      Clause *c = proof[i]->clause ();
      mark_core (c);
      drup_db[c].lemma = false;
    }
}

/*------------------------------------------------------------------------*/

void Drupper::assume_negation (Clause *lemma) {
  assert (in_action && !internal->level);
  assert (lemma && core (lemma));
  assert (internal->propagated == internal->trail.size ());

  vector<int> decisions;
  for (int lit : *lemma)
    if (!internal->val (lit))
      decisions.push_back (-lit);

  assert (decisions.size ());
  internal->search_assume_multiple_decisions (decisions);
  assert (internal->level == int (decisions.size ()));
}

bool Drupper::propagate_conflict () {
  START (drup_propagate);
  assert (!internal->conflict);
  if (internal->propagate ()) {
    START (drup_repropagate);
    {
      // If propagate fails, it may be due to incrementality and
      // missing units. re-propagate the entire trail.
      /// TODO: Understand what exactly happens and why is this needed.
      // A good point to start: test/trace/reg0048.trace.
      // assert (stats.trims > 1);
    }
    internal->propagated = 0;
    if (internal->propagate ()) {
      internal->backtrack ();
      return false;
    }
    STOP (drup_repropagate);
  }
  STOP (drup_propagate);
  return true;
}

bool Drupper::reverse_unit_propagation (Clause *c) {
  assume_negation (c);
  return propagate_conflict ();
}

bool Drupper::got_value_by_propagation (int lit) const {
  assert (lit && internal->val (lit) != 0);
#ifndef NDEBUG
  int trail = internal->var (lit).trail;
  assert (trail >= 0 && trail < int (internal->trail.size ()));
  assert (internal->trail[trail] == -lit);
#endif
  return internal->var (lit).trail > internal->control.back ().trail;
}

void Drupper::conflict_analysis_core () {
  START (drup_analyze);
  Clause *conflict = internal->conflict;
  assert (conflict);
  mark_core (conflict);

#ifndef NDEBUG
  int seen = 0;
#endif

  for (int lit : *conflict) {
    Var &v = internal->var (lit);
    assert (v.level > 0 || v.reason);
    if (got_value_by_propagation (lit)) {
      assert (!internal->flags (lit).seen);
#ifndef NDEBUG
      seen++;
#endif
      internal->flags (lit).seen = true;
    } else if (!v.level)
      mark_core (v.reason);
  }

  for (int i = internal->trail.size () - 1;
       i > internal->control.back ().trail; i--) {
    int lit = internal->trail[i];
    if (!internal->flags (lit).seen)
      continue;

    internal->flags (lit).seen = false;

    Clause *c = internal->var (lit).reason;
    mark_core (c);

#ifndef NDEBUG
    seen--;
    assert (internal->var (c->literals[0]).reason == c);
    assert (internal->val (c->literals[0]) > 0);
    assert (c->literals[0] == lit);
#endif

    for (int j = 1; j < c->size; j++) {
      int lit = c->literals[j];
      Var &v = internal->var (lit);
      assert (internal->val (lit) < 0);
      if (got_value_by_propagation (lit)) {
#ifndef NDEBUG
        if (!internal->flags (lit).seen)
          seen++;
#endif
        internal->flags (lit).seen = true;
      } else if (!v.level) {
        mark_core (v.reason);
      }
    }
  }

#ifndef NDEBUG
  assert (!seen);
#endif

  STOP (drup_analyze);
}

/*------------------------------------------------------------------------*/

void Drupper::mark_core_trail_antecedents () {
  for (int i = internal->trail.size () - 1; i >= 0; i--) {
    int lit = internal->trail[i];
    Clause *reason = internal->var (lit).reason;
    assert (reason);
    if (core (reason)) {
      assert (reason->literals[0] == lit);
      for (int lit : *reason)
        mark_core (internal->var (lit).reason);
      internal->propagated = i;
      /// TODO: set internal->propagated2
    }
  }
}

void Drupper::unmark_core () {
  for (Clause *c : internal->clauses)
    unmark_core (c);
  for (Clause *c : unit_clauses)
    unmark_core (c);
  stats.core.clauses = 0;
  stats.core.lemmas = 0;
  stats.core.variables = 0;
}

void Drupper::restore_trail () {
  lock_scope isolate (isolated);
  // Restoring the trail is done with respect to the order of literals.
  // Each unit is allocated in the same order it's pushed the trail.
  for (Clause *c : unit_clauses) {
    const int lit = c->literals[0];
    if (internal->val (lit))
      continue;
    internal->search_assign (lit, c);
    internal->propagate ();
  }
}

void Drupper::restore_proof_garbage_marks () {
  lock_scope isolate (isolated);

  for (DrupperClause *dc : proof) {
    Clause *c = dc->clause ();
    assert (c);
    if (dc->deleted)
      mark_garbage (c);
    else
      mark_active (c);
    if (!dc->deleted && c->size > 1)
      internal->watch_clause (c);
  }

  if (failed_constraint)
    mark_garbage (failed_constraint);

  if (overconstrained) {
    assert (final_conflict);
    mark_garbage (final_conflict);
  }

  final_conflict = failed_constraint = 0;
}

/*------------------------------------------------------------------------*/

void Drupper::check_environment () const {
#ifndef NDEBUG
  assert (proof.size () == unsigned (stats.derived + stats.deleted));
  for (unsigned i = 0; i < proof.size (); i++) {
    DrupperClause *dc = proof[i];
    assert (dc);
    if (dc->deleted) {
      if (dc->variant_type () == CLAUSE) {
        Clause *c = dc->clause ();
        if (i == proof.size () - 1)
          assert (c && (c->garbage || overconstrained));
        else
          assert (c && c->garbage);
      } else {
        assert (dc->variant_type () == LITERALS);
        assert (dc->variant_type () == LITERALS && dc->lits ().size ());
        if (dc->revive_at) {
          assert (dc->revive_at <= proof.size ());
          assert (dc->revive_at > 0);
          auto &pdc = proof[dc->revive_at - 1];
          assert (!pdc->revive_at && !pdc->deleted);
          if (pdc->variant_type () == LITERALS)
            assert (proof[dc->revive_at - 1]->lits ().size ());
        }
      }
    } else {
      assert (dc->variant_type () == CLAUSE || dc->lits ().size ());
    }
  }
#endif
}

void Drupper::dump_clauses (bool active) const {
  printf ("DUMP CLAUSES START\n");
  int j = unit_clauses.size () - 1;
  for (int i = internal->clauses.size () - 1; i >= 0; i--) {
    Clause *c = internal->clauses[i];
    if (active && c->garbage && c->size != 2)
      continue;
    printf ("(%d) %s: ", i + j + 1, c->garbage ? "garbage" : "       ");
    printf ("(%lu): ", int64_t (c));
    for (int j = 0; j < c->size; j++)
      printf ("%d ", c->literals[j]);
    printf ("\n");
  }
  for (; j >= 0; j--) {
    Clause *c = unit_clauses[j];
    if (active && c->garbage && c->size != 2)
      continue;
    printf ("(%d) %s: ", j, c->garbage ? "garbage" : "       ");
    printf ("c: ");
    for (int j = 0; j < c->size; j++)
      printf ("%d ", c->literals[j]);
    printf ("\n");
  }
  printf ("DUMP CLAUSES END\n");
}

void Drupper::dump_clause (const Clause *c) const {
  if (!c)
    printf ("0 \n");
  else {
    for (int lit : *c)
      printf ("%d ", lit);
    printf ("\n");
  }
}

void Drupper::dump_clause (const DrupperClause *dc) const {
  assert (dc);
  const auto &lits = dc->lits ();
  for (int i : lits)
    printf ("%d ", i);
  printf ("\n");
}

void Drupper::dump_clause (const vector<int> &c) const {
  for (int i : c)
    printf ("%d ", i);
  printf ("\n");
}

void Drupper::dump_proof () const {
  printf ("DUMP PROOF START\n");
  for (int i = proof.size () - 1; i >= 0; i--) {
    auto &dc = proof[i];
    printf ("(%d) (revive_at %d) %s: ", i, dc->revive_at - 1,
            dc->deleted ? "deleted" : "       ");
    if (dc->variant_type () == LITERALS) {
      auto &lits = dc->lits ();
      for (int l : lits)
        printf ("%d ", l);
    } else {
      Clause *c = proof[i]->clause ();
      printf ("c: ");
      if (!c)
        printf ("0 ");
      else {
        for (int lit : *c)
          printf ("%d ", lit);
        printf ("(%lu) %s %s", int64_t (c), c->garbage ? "(garbage)" : "",
                is_on_trail (c) ? "(reason)" : "");
      }
    }
    printf ("\n");
  }
  printf ("DUMP PROOF END\n");
}

void Drupper::dump_trail () const {
  printf ("DUMP TRAIL START\n");
  auto &trail = internal->trail;
  for (int i = trail.size () - 1; i >= 0; i--)
    printf ("(%d) %d <-- ", i, trail[i]),
        dump_clause (internal->var (trail[i]).reason);
  printf ("DUMP TRAIL END\n");
}

/*------------------------------------------------------------------------*/

// Must be called at a point in which no literals are marked!
static vector<int> remove_duplicates (Internal *internal,
                                      const vector<int> &c) {
  vector<int> unique;
  for (int lit : c) {
    if (internal->marked (lit))
      continue;
    internal->mark (lit);
    unique.push_back (lit);
  }
  for (int lit : unique)
    internal->unmark (lit);
  return unique;
}

static void swap_falsified_literals_right (Internal *internal,
                                           vector<int> &c) {
  int sz = c.size ();
  for (int i = 0; i < sz; i++) {
    if (internal->val (c[i]) < 0) {
      int bl = c[--sz];
      c[sz] = c[i];
      c[i] = bl;
    }
  }
}

/*------------------------------------------------------------------------*/

void Drupper::add_derived_clause (Clause *c) {
  if (isolated)
    return;
  assert (!in_action);
  START (drup_inprocess);
  LOG (c, "DRUPPER derived clause notification");
  append_lemma (new DrupperClause (c));
  STOP (drup_inprocess);
}

void Drupper::add_derived_unit_clause (const int lit, bool original) {
  if (isolated)
    return;
  assert (!in_action);
  START (drup_inprocess);
  LOG ({lit}, "DRUPPER derived clause notification");
  assert (lit);
  assert (!original || !internal->var (lit).reason);
  Clause *c = 0;
  if (!internal->var (lit).reason)
    internal->var (lit).reason = c = new_unit_clause (lit, original);
  if (!original) {
    c = !c ? new_unit_clause (lit, original) : c;
    internal->var (lit).reason = c;
    append_lemma (new DrupperClause (c));
  }
  assert (internal->var (lit).reason->literals[0] == lit);
  STOP (drup_inprocess);
}

void Drupper::add_derived_empty_clause () {
  if (isolated)
    return;
  assert (!in_action);
  START (drup_inprocess);
  final_conflict = internal->conflict;
  assert (final_conflict);
  LOG ("DRUPPER derived empty clause notification");
  STOP (drup_inprocess);
}

void Drupper::add_falsified_original_clause (const vector<int> &clause,
                                             bool derived) {
  if (isolated)
    return;
  assert (!in_action && !final_conflict);
  START (drup_inprocess);
  if (derived) {
    // Last deleted lemma is a falsified original.
    // Revive it and mark it as the conflict clause.
    assert (proof.size ());
    DrupperClause *dc = proof.back ();
    vector<int> &lits = dc->lits ();
    if (lits.size () == 1)
      dc->set_variant (new_unit_clause (lits[0], false));
    else
      revive_clause (proof.size () - 1);
    final_conflict = dc->clause ();
    overconstrained = true;
  } else {
    // See discussion in Drupper::delete_clause (const vector<int> &, bool);
    vector<int> modified = remove_duplicates (internal, clause);
    swap_falsified_literals_right (internal, modified);
    if (modified.size () == 1)
      final_conflict = new_unit_clause (modified[0], true);
    else {
      final_conflict = new_redundant_clause (modified);
      internal->watch_clause (final_conflict);
      for (int lit : *final_conflict)
        if (internal->flags (lit).eliminated ())
          internal->reactivate (lit);
    }
  }
  assert (final_conflict);
  LOG ("DRUPPER derived empty clause notification");
  STOP (drup_inprocess);
}

void Drupper::add_failing_assumption (const vector<int> &c) {
  if (isolated)
    return;
  assert (!in_action);
  if (c.size () == 1) {
    Clause *r = internal->var (c[0]).reason;
    if (r)
      mark_core (r);
  } else
    failing_assumptions.push_back (c);
}

void Drupper::add_updated_clause (Clause *c) {
  if (isolated)
    return;
  assert (!in_action && c);
  START (drup_inprocess);
  LOG (c, "DRUPPER updated");
  unsigned revive_at = drup_db[c].idx;
  if (revive_at) {
    assert (proof[revive_at - 1]->clause () == c);
    proof[revive_at - 1]->set_variant (0);
  }
  append_lemma (new DrupperClause (c));
  vector<int> lits;
  for (int lit : *c)
    lits.push_back (lit);
  DrupperClause *old = new DrupperClause (lits, true);
  old->revive_at = revive_at;
  append_lemma (old);
  STOP (drup_inprocess);
}

/*------------------------------------------------------------------------*/

void Drupper::delete_clause (const vector<int> &c, bool original) {
  if (isolated)
    return;
  assert (!in_action);
  START (drup_inprocess);
  LOG (c, "DRUPPER clause deletion notification");
  // remove duplicates. if there is only one unique literal,
  // skip it unless it's a falsified original then we cache it.
  vector<int> modified = remove_duplicates (internal, c);
  if (modified.size () == c.size () || modified.size () > 1) {
    if (original) {
      /// NOTE: This is an original clause that has been reduced to an
      /// irredundant
      // dervied clause after removing all its falsified literals. This
      // clause was not allocated in memory. However, it needs to be revived
      // for correct core extraction and complete validation. Moving the
      // falsified literals to the end of the clause is crucial as we need
      // to watch the first two unassigned literals of this clause once it
      // is revived.
      swap_falsified_literals_right (internal, modified);
    }
    append_lemma (new DrupperClause (modified, true));
  }
  STOP (drup_inprocess);
}

void Drupper::delete_clause (Clause *c) {
  if (isolated)
    return;
  assert (!in_action);
  START (drup_inprocess);
  LOG (c, "DRUPPER clause deletion notification");
  append_lemma (new DrupperClause (c, true));
  STOP (drup_inprocess);
}

void Drupper::deallocate_clause (Clause *c) {
  if (isolated || c->moved || !drup_db[c].idx)
    return;
  assert (!in_action);
  START (drup_inprocess);
  LOG (c, "DRUPPER clause deallocation notification");
  assert (c && drup_db[c].idx && drup_db[c].idx <= proof.size ());
  auto &dc = proof[drup_db[c].idx - 1];
  assert (dc->clause () == c);
  dc->flip_variant ();
  if (dc->revive_at) {
    auto &pdc = proof[dc->revive_at - 1];
    assert (pdc->clause () == c && !pdc->deleted);
    pdc->set_variant (0);
  }
  drup_db.erase (c);
  STOP (drup_inprocess);
}

/*------------------------------------------------------------------------*/

void Drupper::update_moved_counterparts () {
  if (isolated)
    return;
  assert (!in_action);
  START (drup_inprocess);
  for (unsigned i = 0; i < proof.size (); i++) {
    auto &dc = proof[i];

    if (dc->variant_type () == LITERALS)
      continue;

    Clause *c = dc->clause ();
    if (!c || !c->moved)
      continue;

#ifndef NDEBUG
    assert (c->copy && c != c->copy);
#endif

    drup_db[c->copy].idx = i+1;
    dc->set_variant (c->copy);
    drup_db.erase (c);
  }

  if (final_conflict && final_conflict->moved)
    final_conflict = final_conflict->copy;

  if (failed_constraint && failed_constraint->moved)
    failed_constraint = failed_constraint->copy;

  STOP (drup_inprocess);
}

/*------------------------------------------------------------------------*/

void Drupper::trim_ () {

  START (drup_trim);
  LOG ("DRUPPER trim");

  stats.trims++;
  check_environment ();

  mark_conflict ();

  internal->flush_all_occs_and_watches ();
  clean_conflict ();
  // 'trail_sz' is used for lazy shrinking of the trail.
  unsigned trail_sz = internal->trail.size ();

  lock_scope trim_scope (in_action);

  // Main trimming loop
  for (int i = proof.size () - 1 - (overconstrained); i >= 0; i--) {
    auto &dc = proof[i];
    bool deleted = dc->deleted;

    if (deleted) {
      revive_clause (i);
      continue;
    }

    Clause *c = dc->clause ();
    assert (c && !c->garbage);

    if (is_on_trail (c)) {
      if (settings.core_units)
        mark_core (c);
      undo_trail_core (c, trail_sz);
      if (settings.report)
        internal->report ('m');
    }

    drup_db[c].lemma = true;
    stagnate_clause (c);

    if (core (c)) {
      shrink_internal_trail (trail_sz);
      bool validated = reverse_unit_propagation (c);
      assert (validated);
      conflict_analysis_core ();
      clean_conflict ();
    }
  }

  shrink_internal_trail (trail_sz);
  mark_core_trail_antecedents ();

#ifndef NDEBUG
  if (settings.check_core) {
    // Verify the set of core clauses is UNSAT using a fresh
    // new solver.
    CoreVerifier v;
    ((const Drupper *) this)->traverse_core (v);
    assert (v.verified ());
  }
#endif

  if (settings.report) {
    // Report formula has been succesfully trimmed
    internal->report ('M');
  }

  STOP (drup_trim);
}

void Drupper::trim (ClauseIterator &it) {

  if (internal->external_prop)
    return;

  assert (!in_action && !isolated && !setup_internal_options ());
  save_scope<bool> recover_unsat (internal->unsat);

  trim_ ();

  {
    // This is a good point to handle core clauses as some might be
    // collected later.
    // Traverse core with user provided iterator and collect core
    // statistics.
    traverse_core (it);

    if (settings.dump) {
      CorePrinter printer (internal, "/home/basel.khouri/core",
                           internal->max_var, stats.core.clauses);
      ((const Drupper *) this)->traverse_core (printer);
    }
  }

  if (settings.incremental) {
    restore_proof_garbage_marks ();
    unmark_core ();
    failing_assumptions.clear ();
    restore_trail ();
  }
}

bool Drupper::traverse_core (ClauseIterator &it) {

  vector<int> eclause;
  vector<char> seen (internal->max_var + 1, 0);

  for (Clause *c : internal->clauses)
    if (core (c)) {
      if (c == failed_constraint)
        continue;
      if (lemma (c)) {
        stats.core.lemmas++;
        continue;
      } else
        stats.core.clauses++;
      for (const auto ilit : *c) {
        eclause.push_back (internal->externalize (ilit));
        if (seen[abs (ilit)])
          continue;
        seen[abs (ilit)] = 1;
        stats.core.variables++;
      }
      if (!it.clause (eclause))
        return false;
      eclause.clear ();
    }

  for (Clause *c : unit_clauses)
    if (core (c)) {
      int ilit = c->literals[0];
      if (lemma (c)) {
        stats.core.lemmas++;
        continue;
      } else
        stats.core.clauses++;
      eclause.push_back (internal->externalize (ilit));
      if (!seen[abs (ilit)]) {
        seen[abs (ilit)] = 1;
        stats.core.variables++;
      }
      if (!it.clause (eclause))
        return false;
      eclause.clear ();
    }

  for (int ilit : internal->assumptions)
    if (internal->failed (ilit)) {
      stats.core.clauses++;
      eclause.push_back(internal->externalize (ilit));
      if (!it.clause (eclause))
        return false;
      eclause.clear ();
      if (seen[abs (ilit)])
        continue;
      seen[abs (ilit)] = 1;
      stats.core.variables++;
    }

  for (auto &c : failing_assumptions) {
    stats.core.clauses++;
    for (int ilit : c) {
      eclause.push_back(internal->externalize (ilit));
      if (seen[abs (ilit)])
        continue;
      seen[abs (ilit)] = 1;
      stats.core.variables++;
    }
    if (!it.clause (eclause))
      return false;
    eclause.clear ();
  }

  if (internal->unsat_constraint) {
    stats.core.clauses++;
    for (int ilit : internal->constraint) {
      eclause.push_back (internal->externalize (ilit));
      if (seen[abs (ilit)])
        continue;
      seen[abs (ilit)] = 1;
      stats.core.variables++;
    }
    if (!it.clause (eclause))
      return false;
    eclause.clear ();
  }

  stats.save_core_phase ();

  return true;
}

bool Drupper::traverse_core (ClauseIterator &it) const {

  vector<int> eclause;

  for (Clause *c : internal->clauses)
    if (core (c)) {
      if (lemma (c) || c == failed_constraint)
        continue;
      for (const auto ilit : *c)
        eclause.push_back (internal->externalize (ilit));
      if (!it.clause (eclause))
        return false;
      eclause.clear ();
    }

  for (Clause *c : unit_clauses)
    if (core (c)) {
      int ilit = c->literals[0];
      if (lemma (c))
        continue;
      eclause.push_back (internal->externalize (ilit));
      if (!it.clause (eclause))
        return false;
      eclause.clear ();
    }

  for (int ilit : internal->assumptions)
    if (internal->failed (ilit)) {
      eclause.push_back (internal->externalize (ilit));
      if (!it.clause (eclause))
        return false;
      eclause.clear ();
    }

  for (auto &c : failing_assumptions) {
    for (int ilit : c)
      eclause.push_back(internal->externalize (ilit));
    if (!it.clause (eclause))
      return false;
    eclause.clear ();
  }

  if (internal->unsat_constraint) {
    for (int ilit : internal->constraint)
      eclause.push_back (internal->externalize (ilit));
    if (!it.clause (eclause))
      return false;
    eclause.clear ();
  }

  return true;
}

/// FIXME: experimental trivial implementation... Needs refactoring.
void Drupper::prefer_core_watches (const int lit) {
  auto &ws = internal->watches (lit);
  int l = 0, h = ws.size () - 1;
  while (l < h) {
    auto w = ws[h];
    if (!core (w.clause)) {
      h--;
      continue;
    }
    auto tw = ws[l];
    ws[l++] = ws[h];
    ws[h] = tw;
  }
}

} // namespace CaDiCaL
