#include "internal.hpp"

#define COLOR_UNDEF 0

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

void Internal::drup () {
  assert (!drupper);
  drupper = new Drupper (this);
}

void Internal::trim (ClauseIterator &it) {
  assert (drupper);
  drupper->trim (it);
}

void Internal::trim_and_replay (ClauseIterator *core_it, ResolutionIterator &proof_it) {
  assert (drupper);
  drupper->trim_and_replay (core_it, proof_it);
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

DrupperClauseIterator::DrupperClauseIterator (const vector<int> &clause,
                                              size_t index)
    : m_clause (clause), m_index (index) {}

int DrupperClauseIterator::operator* () const {
  assert (m_index < m_clause.size () - 1);
  return m_clause[m_index];
}

DrupperClauseIterator &DrupperClauseIterator::operator++ () {
  ++m_index;
  return *this;
}

DrupperClauseIterator &DrupperClauseIterator::operator+ (int index) {
  m_index += index;
  return *this;
}

bool DrupperClauseIterator::operator!= (
    const DrupperClauseIterator &other) const {
  return m_index != other.m_index;
}

/*------------------------------------------------------------------------*/

ColorRange::ColorRange () : m_min (COLOR_UNDEF), m_max (COLOR_UNDEF) {}

ColorRange::ColorRange (const unsigned c) : m_min (c), m_max (c) {}

bool ColorRange::undef () const { return m_min == COLOR_UNDEF; }

void ColorRange::reset () {
  m_min = COLOR_UNDEF;
  m_max = COLOR_UNDEF;
}

bool ColorRange::singleton () const { return m_min == m_max; }

void ColorRange::join (const unsigned np) {
  if (np == 0)
    return;
  if (undef ()) {
    m_min = np;
    m_max = np;
  } else if (np > m_max)
    m_max = np;
  else if (np < m_min)
    m_min = np;
}

void ColorRange::join (const ColorRange &o) {
  if (o.undef ())
    return;
  join (o.min ());
  join (o.max ());
}

unsigned ColorRange::min () const { return m_min; }

unsigned ColorRange::max () const { return m_max; }

bool ColorRange::operator== (const ColorRange &r) {
  return m_min == r.min () && m_max == r.max ();
}

bool ColorRange::operator!= (const ColorRange &r) { return !(*this == r); }

void ColorRange::operator= (int code) {
  m_min = (code & 0xFFFF);
  m_max = ((code >> 16) & 0xFFFF);
}

int ColorRange::code () const { return (m_max << 16) | m_min; }

/*------------------------------------------------------------------------*/

class TraceCheck : public ResolutionIterator {
private:
  File *file;
  // Map clause id to trace id
  unordered_map<int, int> trace_id;
  int latest_ids;

  void output (int lit) {
    file->put (lit);
    file->put (" ");
  }

  void output (const vector<int> &c) {
    for (int lit : c)
      output (lit);
  }

  void output (const ChainDerivation &chain) {
    const unsigned pivots_size = chain.pivots.size ();
    assert (chain.clauses.size () == pivots_size + 1);
    output (trace_id[chain.clauses[0].second]);
    for (unsigned i = 0; i < pivots_size; i++)
      output (trace_id[chain.clauses[i + 1].second]);
  }

  void traverse_antecedents (const ChainDerivation &chain) {

    assert (chain.clauses.size () && chain.clauses.size () == chain.pivots.size () + 1);

    const auto pivots_size = chain.pivots.size ();

    if (!trace_id[chain.clauses[0].second]) {
      output (latest_ids);
      trace_id[chain.clauses[0].second] = latest_ids++;
      output (chain.clauses[0].first);
      file->put ("0 0\n");
    }

    for (unsigned i = 0; i < pivots_size; i++)
      if (!trace_id[chain.clauses[i + 1].second]) {
        output (latest_ids);
        trace_id[chain.clauses[i + 1].second] = latest_ids++;
        output (chain.clauses[i + 1].first);
        file->put ("0 0\n");
      }
  }

public:
  TraceCheck (Internal *internal, const char *path) : latest_ids (1) {
    file = File::write (internal, path);
  }

  ~TraceCheck () { delete file; }

  bool resolvent (const ChainDerivation &chain, const vector<int> &parent, int id) {

    traverse_antecedents (chain);

    output (latest_ids);
    trace_id[id] = latest_ids;
    output (parent);
    latest_ids++;

    file->put ("0 ");
    output (chain);
    file->put ("0\n");

    return true;
  }

  bool empty_resolvent (const ChainDerivation &chain) {

    traverse_antecedents (chain);

    output (latest_ids++);

    file->put ("0 ");
    output (chain);
    file->put ("0\n");

    return true;
  }
};

/*------------------------------------------------------------------------*/

LiteralSort::LiteralSort (Internal *i) : internal (i) {}

bool LiteralSort::operator() (int x, int y) const {
  int level_x = internal->var (x).level;
  int level_y = internal->var (y).level;

  if (level_x > level_y)
    return true;
  if (level_x < level_y)
    return false;

  const int val_x = internal->val (x);
  const int val_y = internal->val (y);

  if (!val_x)
    return true;
  if (!val_y)
    return false;
  assert (val_x && val_y);
  if (val_x > 0)
    return val_y < 0 ? true : x < y;
  assert (val_x < 0);
  return val_y > 0 ? false : x < y;
}

/*------------------------------------------------------------------------*/

DrupperClause::DrupperClause (vector<int> c, int code, bool deletion)
    : deleted (deletion), revive_at (0) {
  assert (c.size ());
  variant = LITERALS;
  literals = new std::vector<int> (c);
  literals->push_back (code);
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

Clause *DrupperClause::flip_variant (int code) {
  Clause *ref = counterpart;
  assert (ref);
  destroy_variant ();
  variant = LITERALS;
  literals = new std::vector<int> ();
  for (int lit : *ref)
    literals->push_back (lit);
  literals->push_back (code);
  return ref;
}

Clause *DrupperClause::clause () {
  assert (variant_type () == CLAUSE);
  return counterpart;
}

const vector<int> &DrupperClause::lits () const {
  assert (variant_type () == LITERALS && literals);
  return *literals;
}

int DrupperClause::color_range_code () const {
  assert (variant_type () == LITERALS && literals);
  return (*literals)[literals->size () - 1];
}

int DrupperClause::size () const {
  if (variant_type () == LITERALS) {
    assert (literals && literals->size () > 1);
    return literals->size () - 1;
  } else {
    assert (counterpart);
    return counterpart->size;
  }
}

DrupperClauseIterator DrupperClause::lits_begin () const {
  assert (variant_type () == LITERALS);
  assert (literals && literals->size () > 1);
  return DrupperClauseIterator (*literals, 0);
}

DrupperClauseIterator DrupperClause::lits_end () const {
  assert (variant_type () == LITERALS);
  assert (literals && literals->size () > 1);
  return DrupperClauseIterator (*literals, literals->size () - 1);
}

/*------------------------------------------------------------------------*/

Drupper::Drupper (Internal *i)
    : internal (i), failed_constraint (0), final_conflict (0), isolated (0),
      in_action (0), overconstrained (0), max_color (1) {
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
  updated |= opts.block;
  updated |= opts.compact;
  updated |= opts.checkproof;
  opts.chrono = 0;
  opts.probe = 0;
  opts.block = 0;
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

  c->id = ++internal->clause_id;

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

Clause *Drupper::new_redundant_clause (const DrupperClause *dc) {

  assert (dc && dc->size () <= INT_MAX);
  const int size = (int) dc->size ();
  assert (size >= 2);

  size_t bytes = Clause::bytes (size);
  Clause *c = (Clause *) new char[bytes];

  c->id = ++internal->clause_id;

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

  range (c) = dc->color_range_code ();

  auto it = dc->lits_begin ();
  auto end = dc->lits_end ();
  for (int i = 0; i < size; i++, ++it) {
    assert (it != end);
    c->literals[i] = *it;
  }

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
  c->id = ++internal->clause_id;

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
  lemma (c, !original);
  c->used = c->glue = 0;
  c->size = 1;
  c->pos = 2;
  c->literals[0] = lit;

  assert (c->bytes () == bytes);

  unit_clauses.push_back (c);
  LOG (c, "new pointer %p", (void *) c);

  return c;
}

void Drupper::delete_garbage_unit_clauses () {
  const auto end = unit_clauses.end ();
  auto j = unit_clauses.begin (), i = j;
  while (i != end) {
    Clause *c = *j++ = *i++;
    assert (c);
    if (!c->garbage || is_on_trail (c))
      continue;
    delete[] (char *) c;
    j--;
  }
  unit_clauses.resize (j - unit_clauses.begin ());
}

/*------------------------------------------------------------------------*/

bool Drupper::clauses_are_identical (Clause *c,
                                     const vector<int> &lits) const {
  assert (c);
  if (c->size != lits.size ())
    return false;
  bool identical = true;
  internal->mark (c);
  for (int lit : lits)
    if (!internal->marked (lit))
      identical = false;
  internal->unmark (c);
  return identical;
}

void Drupper::append_lemma (DrupperClause *dc) {
  assert (proof.size () <= (1u << 30) - 1 &&
          "Possible overflow in revive_at/drup.idx members!");
  if (dc->deleted)
    stats.deleted++;
  else
    stats.derived++;
  if (dc->variant_type () == CLAUSE) {
    Clause *c = dc->clause ();
    unsigned c_idx = idx (c);
    if (c_idx && dc->deleted) {
      assert (proof[c_idx - 1]->clause () == c);
      dc->revive_at = c_idx;
    }
#ifndef NDEBUG
    // Ensure reason clause is not deleted.
    int lit = c->literals[0];
    if (internal->fixed (lit) && internal->var (lit).reason == c)
      assert (!c->garbage);
#endif
    idx (c, proof.size () + 1);
    assert (!core (c));
  }
  proof.push_back (dc);
}

void Drupper::revive_clause (const int i) {
  assert (i >= 0 && i < proof.size ());
  DrupperClause *dc = proof[i];
  assert (dc->deleted);
  Clause *c = nullptr;
  if (dc->variant_type () == CLAUSE)
    c = dc->clause ();
  else {
    c = new_redundant_clause (dc);
    mark_garbage (c);
    idx (c, i+1);
    dc->set_variant (c);
  }
  assert (c && c->garbage);
  mark_active (c);
  // This is a hack to easily identify the original core.
  // A revived clause is marked as an original clause.
  // If it's a learnt lemma, it will be marked later on
  // in the the main trimming loop.
  lemma (c, false);
  internal->watch_clause (c);
  for (int lit : *c)
    if (internal->flags (lit).eliminated ())
      internal->reactivate (lit);
  if (dc->revive_at) {
#ifndef NDEBUG
    int j = dc->revive_at - 1;
    assert (j < i && j >= 0);
    assert (!proof[j]->revive_at);
    assert (!proof[j]->deleted);
#endif
    proof[dc->revive_at - 1]->set_variant (c);
  }
  stats.revived++;
}

void Drupper::stagnate_clause (Clause *c) {
  assert (!c->garbage && "remove this if you are actually delaying the "
                          "trace of garbage binaries");
  assert (!c->moved);
  mark_garbage (c);
  /// TODO: Avoid calling unwatch_clause () and try flushing watches before
  /// propagating instead.
  if (c->size > 1)
    internal->unwatch_clause (c);
}

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

void Drupper::reactivate (Clause *c) {
  assert (c);
  for (int lit : *c) {
    auto &f = internal->flags (lit);
    if (f.active () || internal->val (lit))
      continue;
    internal->reactivate (lit);
  }
}

bool Drupper::satisfied (Clause *c) {
  assert (c);
  for (int lit : *c)
    if (internal->val (lit) > 0)
      return true;
  return false;
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
      core (r, true);

    if (core (r))
      for (int j = 1; j < r->size; j++)
        core (internal->var (r->literals[j]).reason, true);
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

void Drupper::lemma (Clause *c, bool val) {
  assert (c);
  drup_db[c].lemma = val;
}

bool Drupper::core (Clause *c) const {
  assert (c);
  bool val = false;
  const auto it = drup_db.find(c);
  if (it != drup_db.end ())
    val = it->second.core;
  return val;
}

void Drupper::core (Clause *c, bool val) {
  assert (c);
  drup_db[c].core = val;
}

unsigned Drupper::idx (Clause *c) const {
  assert (c);
  unsigned val = 0;
  const auto it = drup_db.find(c);
  if (it != drup_db.end ())
    val = it->second.idx;
  return val;
}

void Drupper::idx (Clause *c, unsigned val) {
  assert (c);
  drup_db[c].idx = val;
}

void Drupper::erase (Clause *c) {
  assert (c);
  drup_db.erase (c);
  clause_ranges.erase (c->id);
}

void Drupper::mark_conflict_lit (const int l) {
  assert (internal->val (l) < 0);
  Var &v = internal->var (l);
  Clause *reason = v.reason;
  if (reason)
    core (reason, true);
}

// Detect negated literals in a clause.
static bool tautology (const vector <int> & c) {
  struct {
    bool operator () (const int & a, const int & b) {
      return (abs (a) < abs (b)) || (abs (a) == abs (b) && a < b);
    }
  } sorter;
  auto sorted (c);
  std::sort (sorted.begin (), sorted.end (), sorter);
  for (unsigned i = 1; i < sorted.size (); i++)
    if (sorted[i] == -sorted[i-1])
      return true;
  return false;
}

void Drupper::mark_conflict () {
  if (internal->unsat) {
    assert (final_conflict);
    core (final_conflict, true);
    for (int lit : *final_conflict)
      mark_conflict_lit (lit);
  } else {
    if (internal->unsat_constraint && internal->constraint.size () > 1) {
      failed_constraint = new_redundant_clause (internal->constraint);
      core (failed_constraint, true);
      internal->watch_clause (failed_constraint);
    }
    if (!internal->marked_failed) {
      internal->failing ();
      internal->marked_failed = true;
    }
    for (const auto &failed : failing_assumptions) {
      assert(!overconstrained); // it is possible?
      if (failed.size () == 1) {
        Clause *r = internal->var (failed[0]).reason;
        if (r)
          core (r, true);
        continue;
      }
      if (tautology (failed))
        continue;
      Clause *c = new_redundant_clause (failed);
      internal->watch_clause (c);
      append_lemma (new DrupperClause (c));
      assign_range (c);
      core (c, true);
    }
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
  core (conflict, true);

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
      core (v.reason, true);
  }

  for (int i = internal->trail.size () - 1;
       i > internal->control.back ().trail; i--) {
    int lit = internal->trail[i];
    if (!internal->flags (lit).seen)
      continue;

    internal->flags (lit).seen = false;

    Clause *c = internal->var (lit).reason;
    core (c, true);

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
        core (v.reason, true);
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
        core (internal->var (lit).reason, true);
      internal->propagated = i;
      /// TODO: set internal->propagated2
    }
  }
}

void Drupper::unmark_core () {
  for (Clause *c : internal->clauses)
    core (c, false);
  for (Clause *c : unit_clauses)
    core (c, false);
  stats.core.clauses = 0;
  stats.core.lemmas = 0;
  stats.core.variables = 0;
}

void Drupper::restore_trail (bool initial_data_base) {
  lock_scope isolate (isolated);
  // Restoring the trail is done with respect to the order of literals.
  // Each unit is allocated in the same order it's pushed the trail.
  internal->propagate ();

  {
    // Need to handle cases where constraint is resolved with an assumption
    // This resolution step needs to be justified.
    // for (int lit : internal->assumptions) {
    //   if (!internal->failed (lit) || internal->val (lit))
    //     continue;
    //   internal->search_assign (lit, 0);
    //   internal->propagate ();
    // }
  }
  for (Clause *c : unit_clauses) {
    if (initial_data_base && (lemma (c)))
      continue;
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
        assert (dc->variant_type () == LITERALS && dc->size ());
        if (dc->revive_at) {
          assert (dc->revive_at <= proof.size ());
          assert (dc->revive_at > 0);
          auto &pdc = proof[dc->revive_at - 1];
          assert (!pdc->revive_at && !pdc->deleted);
          if (pdc->variant_type () == LITERALS)
            assert (proof[dc->revive_at - 1]->size ());
        }
      }
    } else {
      assert (dc->variant_type () == CLAUSE || dc->size ());
    }
  }
#endif
}

void Drupper::dump_clauses (bool active) {
  printf ("DUMP CLAUSES START\n");
  int j = unit_clauses.size () - 1;
  for (int i = internal->clauses.size () - 1; i >= 0; i--) {
    Clause *c = internal->clauses[i];
    if (active && c->garbage && c->size != 2)
      continue;
    printf ("%4d) %s %s (%d, %d): ", i + j + 1,
            c->garbage ? "garbage" : "       ",
            core (c) ? "core" : "    ", range (c).min (),
            range (c).max ());
    printf ("(%lu): ", int64_t (c));
    for (int j = 0; j < c->size; j++)
      printf ("%d ", c->literals[j]);
    printf ("\n");
  }
  for (; j >= 0; j--) {
    Clause *c = unit_clauses[j];
    if (active && c->garbage && c->size != 2)
      continue;
    printf ("%4d) %s %s (%d, %d): ", j + 20,
            c->garbage ? "garbage" : "       ",
            core (c) ? "core" : "    ", range (c).min (),
            range (c).max ());
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
  int size = dc->size ();
  auto it = dc->lits_begin ();
  auto end = dc->lits_end ();
  for (int i = 0; i < size; i++, ++it) {
    assert (it != end);
    printf ("%d ", *it);
  }
  printf ("\n");
}

void Drupper::dump_clause (const vector<int> &c) const {
  for (int i : c)
    printf ("%d ", i);
  printf ("\n");
}

void Drupper::dump_proof () {
  printf ("DUMP PROOF START\n");
  for (int i = proof.size () - 1; i >= 0; i--) {
    auto &dc = proof[i];
    printf ("(%d) (revive_at %d) %s: ", i, dc->revive_at - 1,
            dc->deleted ? "deleted" : "       ");
    if (dc->variant_type () == LITERALS) {
      int size = dc->size ();
      auto it = dc->lits_begin ();
      auto end = dc->lits_end ();
      for (int i = 0; i < size; i++, ++it) {
        assert (it != end);
        printf ("%d ", *it);
      }
      ColorRange cr = dc->color_range_code ();
      printf (" (%d, %d)", cr.min (), cr.max ());
    } else {
      Clause *c = proof[i]->clause ();
      printf ("c: ");
      if (!c)
        printf ("0 ");
      else {
        for (int lit : *c)
          printf ("%d ", lit);
        printf ("(%lu) %s %s %s", int64_t (c),
                c->garbage ? "(garbage)" : "",
                is_on_trail (c) ? "(reason)" : "",
                core (c) ? "(core)" : "");
      }
      const ColorRange &cr = c ? range (c) : ColorRange ();
      printf (" (%d, %d)", cr.min (), cr.max ());
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
  assign_range (c);
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
    if (dc->size () == 1)
      dc->set_variant (new_unit_clause (*dc->lits_begin(), false));
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
    assign_range (final_conflict);
  }
  assert (final_conflict);
  LOG ("DRUPPER derived empty clause notification");
  STOP (drup_inprocess);
}

void Drupper::clear_failing_assumption () {
  if (isolated)
    return;
  failing_assumptions.clear ();
}

void Drupper::add_failing_assumption (const vector<int> &failed) {
  if (isolated)
    return;
  failing_assumptions.push_back (failed);
}

void Drupper::add_failing_assumption (int failed) {
  if (isolated)
    return;
  assert (!in_action);
  Clause *r = internal->var (failed).reason;
  if (r)
    core (r, true);
}

void Drupper::add_updated_clause (Clause *c) {
  if (isolated)
    return;
  assert (!in_action && c);
  START (drup_inprocess);
  LOG (c, "DRUPPER updated");
  const unsigned revive_at = idx (c);
  if (revive_at) {
    assert (proof[revive_at - 1]->clause () == c);
    proof[revive_at - 1]->set_variant (0);
  }
  append_lemma (new DrupperClause (c));
  vector<int> lits;
  for (int lit : *c)
    lits.push_back (lit);
  DrupperClause *old =
      new DrupperClause (lits, range (c).code (), true);
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
    assign_range (modified);
    append_lemma (
        new DrupperClause (modified, ColorRange (max_color).code (), true));
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
  if (isolated || c->moved || !idx (c))
    return;
  assert (!in_action);
  START (drup_inprocess);
  LOG (c, "DRUPPER clause deallocation notification");
  assert (c && idx (c) && idx (c) <= proof.size ());
  auto &dc = proof[idx (c) - 1];
  assert (dc->clause () == c);
  dc->flip_variant (range (dc->clause ()).code ());
  if (dc->revive_at) {
    auto &pdc = proof[dc->revive_at - 1];
    assert (pdc->clause () == c && !pdc->deleted);
    pdc->set_variant (0);
  }
  erase (c);
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

    idx (c->copy, i+1);
    dc->set_variant (c->copy);
    erase (c);
  }

  if (final_conflict && final_conflict->moved) {
    erase (final_conflict);
    final_conflict = final_conflict->copy;
  }

  if (failed_constraint && failed_constraint->moved) {
    erase (failed_constraint);
    failed_constraint = failed_constraint->copy;
  }

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
        core (c, true);
      undo_trail_core (c, trail_sz);
      if (settings.report)
        internal->report ('m');
    }

    lemma (c, true);
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

/*------------------------------------------------------------------------*/

ColorRange& Drupper::range(Clause *c) {
  assert (c);
  if (c->size == 1)
    return range (*(c->begin()));
  return clause_ranges[c->id];
}

ColorRange& Drupper::range(int lit) {
  assert (lit && lit <= internal->max_var);
  return variable_ranges[abs(lit)];
}

/*------------------------------------------------------------------------*/

void Drupper::pick_new_color (int c) {
  assert (!in_action && !isolated);
  assert (!c || c > max_color);
  if (!c)
    max_color++;
  else
    max_color = c;
}

void Drupper::init_range (const Clause *c) {
  assert (c);
  const auto it = clause_ranges.find(c->id);
  assert (it != clause_ranges.end ());
  improted_range.join (it->second);
  assert (!improted_range.undef ());
}

void Drupper::join_range (int lit) {
  improted_range.join (range (lit));
  assert (!improted_range.undef ());
}

void Drupper::join_range (Clause *c) {
  improted_range.join (range (c));
  assert (!improted_range.undef ());
}

void Drupper::add_range (Clause *c) {
  if (!c) {
     reset_range ();
     return;
  }
  assert (!improted_range.undef () && c && range (c).undef ());
  assign_range (c, improted_range);
  improted_range.reset ();
}

void Drupper::assign_range (const vector<int> &c) {
  if (isolated)
    return;
  assert (!in_action);
  for (int l : c)
    range (l).join (max_color);
}

void Drupper::assign_range (Clause *c) {
  if (isolated)
    return;
  assert (!in_action && c);
  range (c).join (max_color);
  for (int l : *c)
    range (l).join (max_color);
}

void Drupper::assign_range (Clause *c, ColorRange &cr) {
  if (isolated)
    return;
  assert (!in_action && c);
  range (c).join (cr);
  for (int l : *c)
    range (l).join (cr);
}

void Drupper::assign_range (int lit) {
  if (isolated || in_action)
    return;
  Clause *reason = internal->var (lit).reason;
  assert (reason && !range (reason).undef ());
  auto &unit_color_range = range (lit);
  unit_color_range = range (reason);
  for (int l : *reason)
    unit_color_range.join (range (l));
}

void Drupper::reset_range () {
  improted_range.reset ();
}

/*------------------------------------------------------------------------*/

bool Drupper::unit (Clause *c) {
  assert (c);
  if (internal->val (c->literals[0]))
    return false;
  for (int j = 1; j < c->size; j++)
    if (internal->val (c->literals[j]) >= 0)
      return false;
  return true;
}

bool Drupper::shared (Clause *c) {
  assert (c);
  int max = range (c).max ();
  for (int lit : *c)
    if (range (lit).max () <= max)
      return false;
  return true;
}

bool Drupper::color_ordered_propagate (bool core) {
  assert (settings.ordered_propagate);
  auto &propagated = internal->propagated;
  const auto before = internal->propagated;
  bool res = true;
  for (int i = 1; res && i <= max_color; i++) {
    propagated = before;
    res = internal->propagate (core, i);
  }
  return res;
}

bool Drupper::propagate (bool core) {
  if (settings.ordered_propagate)
    return color_ordered_propagate (core);
  return internal->propagate (core);
}

void Drupper::append_chain_anchor (ChainDerivation &chain, int unit_anchor) {
  assert (unit_anchor);
  vector<int> c = {unit_anchor};
  int &c_id = unit_ids[abs (unit_anchor)];
  if (!c_id)
    c_id = ++internal->clause_id;
  chain.clauses.push_back (make_pair (c, c_id));
}

void Drupper::append_chain_anchor (ChainDerivation &chain, Clause *anchor) {
  assert (anchor);
  vector<int> c;
  for (int l : *anchor)
    c.push_back (l);
  int c_id = anchor->id;
  if (c.size () == 1) {
    // If a unit id is already chached, use it instead.
    // Otherwise, update unit id accordingly.
    if (unit_ids[abs (c[0])])
      c_id = unit_ids[abs (c[0])];
    else
      unit_ids[abs (c[0])] = c_id;
  }
  chain.clauses.push_back (make_pair (c, c_id));
}

void Drupper::append_chain_antecedent (ChainDerivation &chain, Clause *antecedent, int pivot) {
  assert (antecedent && chain.clauses.size ());
  vector<int> c;
  for (int l : *antecedent)
    c.push_back (l);
  int c_id = antecedent->id;
  if (c.size () == 1) {
    // If a unit id is already chached, use it instead.
    // Otherwise, update unit id accordingly.
    if (unit_ids[abs (c[0])])
      c_id = unit_ids[abs (c[0])];
    else
      unit_ids[abs (c[0])] = c_id;
  }
  chain.clauses.push_back (make_pair (c, c_id));
  chain.pivots.push_back (pivot);
  assert (chain.clauses.size () ==  chain.pivots.size () + 1);
}

void Drupper::append_chain_antecedent (ChainDerivation &chain, int unit_antecedent) {
  assert (unit_antecedent && chain.clauses.size ());
  vector<int> c = {unit_antecedent};
  int &c_id = unit_ids[abs (unit_antecedent)];
  if (!c_id)
    c_id = ++internal->clause_id;
  chain.clauses.push_back (make_pair (c, c_id));
  chain.pivots.push_back (unit_antecedent);
  assert (chain.clauses.size () ==  chain.pivots.size () + 1);
}

void Drupper::notify_proof_iterator (ResolutionIterator &it, const ChainDerivation &chain, Clause *p) {
  assert (p);
  vector<int> c;
  for (int l : *p)
    c.push_back (l);
  int c_id = p->id;
  if (c.size () == 1) {
    // If a unit id is already chached, use it instead.
    // Otherwise, update unit id accordingly.
    if (unit_ids[abs (c[0])])
      c_id = unit_ids[abs (c[0])];
    else
      unit_ids[abs (c[0])] = c_id;
  }
  if (!it.resolvent (chain, c, c_id))
    throw ReplayAbort ();
}

void Drupper::notify_proof_iterator (ResolutionIterator &it, const ChainDerivation &chain, int p) {
  assert (p);
  vector<int> c = {p};
  int &c_id = unit_ids[abs (p)];
  if (!c_id)
    c_id = ++internal->clause_id;
  if (!it.resolvent (chain, c, c_id))
    throw ReplayAbort ();
}

Clause *Drupper::recursively_colorize (Clause *anchor, ResolutionIterator &it) {

  assert (anchor);

  vector<int> learnt;
  ColorRange r;
  int color = range (anchor).max ();

  ChainDerivation chain = colorize (anchor, range (anchor).max (), learnt, r, it);

  if (chain.pivots.empty ())
    return anchor;

  assert(r.max() <= color);

  if (clauses_are_identical (anchor, learnt))
    return anchor;

  Clause *resolvent;
  if (learnt.size () == 1)
    resolvent = new_unit_clause (learnt[0], false);
  else {
    std::sort (learnt.begin (), learnt.end (), LiteralSort (internal));
    resolvent = new_redundant_clause (learnt);
    internal->watch_clause (resolvent);
  }

  range (resolvent) = r;
  core (resolvent, true);

  int lit = resolvent->literals[0];
  if (internal->val (lit) > 0)
    internal->var (lit).reason = resolvent;

  notify_proof_iterator (it, chain, resolvent);

  return resolvent;
}

ChainDerivation Drupper::colorize (Clause *reason, int color,
                        vector<int> &learnt, ColorRange &r, ResolutionIterator &it) {

  assert (reason && learnt.empty () && r.undef ());

  vector<char> opened (internal->max_var + 1, 0);
  vector<char> learnt_seen (internal->max_var + 1, 0);
  auto &trail = internal->trail;
  int i = trail.size (), open = 0, uip = 0;
  ChainDerivation chain;

  int lit = reason->literals[0];
  if (internal->val (lit) > 0)
    learnt.push_back (uip = lit);

  for (;;) {
    assert (reason);
    if (range (reason).max () < color) {
      // Attempt to turn into a shared derived clause.
      reason = recursively_colorize (reason, it);
    }
    if (chain.empty ())
      append_chain_anchor (chain, reason);
    else
      append_chain_antecedent (chain, reason, uip);
    r.join (range (reason));
    assert (range (reason).max () <= color);
    for (int other : *reason)
      if (other != uip) {
        assert (other);
        if (opened[abs (other)])
          continue;
        assert (internal->val (other) < 0);
        auto &v = internal->var (other);
        if (v.reason && range (v.reason).max () <= color && got_value_by_propagation (other)) {
          open++;
          opened[abs (other)] = 1;
          continue;
        }
        if (learnt_seen[abs (other)])
          continue;
        learnt_seen[abs (other)] = 1;
        learnt.push_back (other);
      }

    if (!open)
      break;

    uip = 0;
    while (!uip) {
      assert (i > 0);
      const int lit = trail[--i];
      if (!opened[abs (lit)])
        continue;
      uip = lit;
    }
    reason = internal->var (uip).reason;
    opened[abs (uip)] = 0;
    open--;
  }

  assert (chain.clauses.size () == chain.pivots.size () + 1);
  return chain;
}

bool Drupper::skip_derivation (Clause *c) {
  assert (c);

  reactivate (c);

  if (c->garbage) {
    assert (core (c) || !is_on_trail (c));
    if (!core (c) || satisfied (c))
      return true;
  } else {
    if (!core (c)) {
      bool locked = is_on_trail (c);
      assert (!locked || satisfied (c) || core (c));
      if (!locked || satisfied (c))
        stagnate_clause (c);
    }
    return true;
  }

  int *literals = c->literals;
  if (internal->val (literals[0])) {
    for (int j = 1; j < c->size; j++)
      if (!internal->val (literals[j])) {
        int lit = literals[0];
        literals[0] = literals[j];
        literals[j] = lit;
        break;
      }
  }

  assert (c->garbage && core (c) && lemma (c));
  assert (!internal->val (c->literals[0]));

  return false;
}

void Drupper::label_initial (ResolutionIterator &it,
                             int &trail_label_idx, ChainDerivation &chain) {

  auto &trail = internal->trail;
  int trail_sz = trail.size ();

  while (trail_label_idx < trail_sz) {
    const int lit = trail[trail_label_idx++];

    Clause *c = internal->var (lit).reason;

    if (!c) {
      assert (internal->assumed (lit));
      continue;
    }
    assert (c->literals[0] == lit);

    auto &cr = range (c);

    switch (c->size) {
    case 1:
      range (lit) = cr;
      break;
    case 2: {
      int blit = -c->literals[1];
      cr.join (range (blit));
      range (lit) = cr;
      chain.clear ();
      append_chain_anchor (chain, c);
      append_chain_antecedent (chain, blit);
      notify_proof_iterator (it, chain, lit);
    } break;
    default:
      chain.clear ();
      append_chain_anchor (chain, c);
      for (int j = 1; j < c->size; j++) {
        int other = -c->literals[j];
        cr.join (range (other));
        append_chain_antecedent (chain, other);
      }
      range (lit) = cr;
      notify_proof_iterator (it, chain, lit);
    }
  }
}

void Drupper::label_final (ResolutionIterator &it, Clause *source) {
  assert (source);
  ChainDerivation chain;
  append_chain_anchor (chain, source);
  for (int lit : *source)
    append_chain_antecedent (chain, -lit);
  if (!it.empty_resolvent (chain))
    throw ReplayAbort ();
}

void Drupper::label_final_assumptions (ResolutionIterator &it) {
  ChainDerivation chain;
  for (const auto &anchor : failing_assumptions) {
    // dump_clause (anchor);
    assert (anchor.size () > 1);
    // This clause is not actually allocated and therefore can pick new id.
    chain.clauses.push_back (make_pair (anchor, ++internal->clause_id));
    for (int lit : anchor)
      append_chain_antecedent (chain, -lit);
    it.empty_resolvent (chain);
    chain.clear ();
  }
}

void Drupper::replay (ResolutionIterator &it) {

  START (drup_replay);
  LOG ("DRUPPER replay");

  save_scope<bool> recover_unsat (internal->unsat);
  lock_scope replay_scope (in_action);

  assert (unit_ids.empty ());
  unit_ids.resize (internal->max_var + 1, 0);

  vector<Clause *> optimized_proof;
  int trail_label_idx = 0;
  ChainDerivation chain;

  label_initial (it, trail_label_idx, chain);

  const unsigned size = proof.size ();

  for (unsigned i = 0; i < size; i++) {
    auto &dc = proof[i];
    Clause *c = dc->clause ();

    if (skip_derivation (c))
      continue;

    assume_negation (c);
    if (propagate (true)) {
      internal->propagated = 0;
      propagate ();
    }

    Clause *conflict = internal->conflict;
    assert (conflict);

    bool learned = true;
    vector<int> learnt;
    ColorRange cr;
    int color = range (conflict).max ();
    while (color <= max_color) {
      learnt.clear (), cr.reset (), chain.clear ();
      // Attempt to apply only resolutions that are in the color partition
      // as 'conflict'.
      // Clauses from earlier partitions are recursively colorized by
      // attempting to turn them into shared derived clauses. Clauses from
      // later partitions are ignored.
      chain = colorize (conflict, color, learnt, cr, it);

      if (!(learned = chain.pivots.size ())) {
        color++;
        continue;
      }

#if DNDEBUG
      for (int lit : learnt)
        assert (internal->val (lit) < 0);
#endif

      if (clauses_are_identical (c, learnt)) {
        range (c) = cr;
        int sz = c->size;
        std::sort (learnt.begin (), learnt.end (), LiteralSort (internal));
        for (int i = 0; i < sz; i++)
          c->literals[i] = learnt[i];
        mark_active (c);
        notify_proof_iterator (it, chain, c);
        if (c->size > 1)
          internal->watch_clause (c);
        if (settings.optimize_proof) {
          assert (!c->garbage);
          optimized_proof.push_back (c);
        }
        break;
      }

      color = max_color + 1;
      for (int lit : learnt)
        /// FIXME: Does not seem sound to me according to the paper:
        // T = {q in c | reason(q) == nil}
        // if T is empty, then break
        // k <- min{k(q) | q in T}
        // But the check got_value_by_propagation is not the same with
        // reason (q)
        if (got_value_by_propagation (lit)) {
          Clause *r = internal->var (lit).reason;
          assert (r);
          color = min (int (range (r).max ()), color);
        }

      if (learnt.size () == 1)
        conflict = new_unit_clause (learnt[0], false);
      else {
        std::sort (learnt.begin (), learnt.end (), LiteralSort (internal));
        conflict = new_redundant_clause (learnt);
        internal->watch_clause (conflict);
      }
      range (conflict) = cr;
      core (conflict, true);
      if (settings.optimize_proof) {
        assert (!conflict->garbage);
        optimized_proof.push_back (conflict);
      }

      ///FIXME: This is not necessarily true with reordering.
      core (c, false);

      notify_proof_iterator (it, chain, conflict);

      if (color > max_color) {
        // Set drup.idx to 0
        c = conflict;
        dc->set_variant (conflict);
      }
    }

    assert (dc && c && dc->clause () == c);
    clean_conflict ();

    if (!learned) {
      assert (c->garbage && core (c));
      core (c, false);
      continue;
    }

    mark_active (c);

    if (c->size == 1 || internal->val (c->literals[1]) < 0) {
      lock_scope isolate (isolated);
      assert (unit (c));
      internal->search_assign (c->literals[0], c);
      bool conflicting = !propagate (true);
      label_initial (it, trail_label_idx, chain);
      if (conflicting) {
        assert (internal->conflict);
        label_final (it, internal->conflict);
        break;
      }
    }
  }

  if (internal->unsat_constraint) {
    if (failed_constraint) {
      assert (failed_constraint->size > 1);
      label_final (it, failed_constraint);
    } else {
      assert (internal->constraint.size () == 1);
      label_final (it, internal->var (internal->constraint[0]).reason);
    }
  } else
    label_final_assumptions (it);


  if (settings.optimize_proof)
    optimize_proof (optimized_proof);

  STOP (drup_replay);
}

void Drupper::optimize_proof (vector<Clause *> &optimized) {

  while (proof.size ()) {
    DrupperClause *dc = proof.back ();
    Clause *c = dc->clause ();
    assert (c);
    idx (c, 0);
    proof.pop_back ();
    delete dc;
  }

  assert (proof.empty ());

  for (auto &c : optimized) {
    assert (c /*&& !c->garbage && c->drup.core */&& !idx (c));
    append_lemma (new DrupperClause (c));
  }

  assert (proof.size () == optimized.size ());

  stats.derived = proof.size ();
  stats.deleted = 0;
  // stats.optimized = proof.size ();
}

void Drupper::trim_and_replay (ClauseIterator *core_it, ResolutionIterator &proof_it) {

  LOG ("DRUPPER trim_and_replay");

  trim_ ();

  {
    // This is a good point to handle core clauses as some might be
    // collected later.
    // Traverse core with user provided iterator and collect core
    // statistics.
    if (core_it)
      traverse_core (*core_it);

    if (settings.dump) {
      CorePrinter printer (internal, "/home/basel.khouri/core",
                           internal->max_var, stats.core.clauses);
      ((const Drupper *) this)->traverse_core (printer);
    }
  }

  clean_conflict ();
  restore_trail (true /* initial data base only */);

  try {
    lock_scope ordered_propagation (settings.ordered_propagate);
    replay (proof_it);
  } catch (const ReplayAbort& e) {
    // External resolution iterator has returned false and thus we abort.
  }

  lock_scope isolate (isolated);
  internal->delete_garbage_clauses ();
  delete_garbage_unit_clauses ();

  if (settings.incremental) {
    unmark_core ();
    failing_assumptions.clear ();
  }

  if (failed_constraint) {
    assert (!idx (failed_constraint));
    mark_garbage (failed_constraint);
  }

  if (overconstrained) {
    assert (final_conflict && !idx (final_conflict));
    mark_garbage (final_conflict);
  }

  final_conflict = failed_constraint = 0;
}

void Drupper::trace_check (const char *path) {
  TraceCheck proof_it (internal, path);
  struct DummyCore : ClauseIterator {
    bool clause (const vector<int> &c) { return true; }
  } core_it;
  trim_and_replay (&core_it, proof_it);
}

} // namespace CaDiCaL
