// Created by Basel Khouri 2024

#include "drup2itp.hpp"
#include "../src/random.hpp"
#include "../src/util.hpp"

extern "C" {
#include <assert.h>
}

namespace CaDiCaLDRUP2Itp {

inline unsigned Drup2Itp::vlit (int lit) {
  unsigned res = (lit < 0) + 2u * (unsigned) abs (lit);
  return res;
}

inline signed char Drup2Itp::val (int lit) const {
  assert (lit && vals);
  assert (lit != INT_MIN);
  assert (abs (lit) < size_vars);
  assert (vals[lit] == -vals[-lit]);
  return vals[lit];
}

/*------------------------------------------------------------------------*/

Clause *Drup2Itp::new_clause (const vector<int> &literals, uint64_t id,
                              uint64_t hash) {
  const size_t size = literals.size ();
  assert (size <= UINT_MAX);
  const int off = size ? 1 : 0;
  const size_t bytes = sizeof (Clause) + (size - off) * sizeof (int);
  Clause *res = (Clause *) new char[bytes];
  res->next = 0;
  res->hash = hash;
  res->id = id;
  res->garbage = false;
  res->core = false;
  res->original = false;
  res->size = size;
  int *p = res->literals;
  for (int lit : literals)
    *p++ = lit;
  num_clauses++;
  if (literals.size () == 1)
    stats.units++;
  return res;
}

void Drup2Itp::delete_clause (Clause *c) {
  assert (num_clauses);
  num_clauses--;
  delete[] (char *) c;
}

void Drup2Itp::enlarge_clauses () {
  assert (num_clauses == size_clauses);
  const uint64_t new_size_clauses = size_clauses ? 2 * size_clauses : 1;
  Clause **new_clauses;
  new_clauses = new Clause *[new_size_clauses];
  CaDiCaL::clear_n (new_clauses, new_size_clauses);
  for (uint64_t i = 0; i < size_clauses; i++) {
    for (Clause *c = clauses[i], *next; c; c = next) {
      next = c->next;
      const uint64_t h = reduce_hash (c->hash, new_size_clauses);
      c->next = new_clauses[h];
      new_clauses[h] = c;
    }
  }
  delete[] clauses;
  clauses = new_clauses;
  size_clauses = new_size_clauses;
}

/*------------------------------------------------------------------------*/

Drup2Itp::Drup2Itp ()
    : internal (0), top_conflict (0), conflict (0),
      imported_tautological (false), max_var (0), size_vars (0), vals (0),
      inconsistent (false), empty_original_clause (false), num_clauses (0),
      num_watched (0), num_watched_garbage (0), size_clauses (0),
      clauses (0), next_to_propagate (0), detach_eagerly (false) {
  // Initialize random number table for hash function.
  //
  CaDiCaL::Random random (42);
  for (unsigned n = 0; n < num_nonces; n++) {
    uint64_t nonce = random.next ();
    if (!(nonce & 1))
      nonce++;
    assert (nonce), assert (nonce & 1);
    nonces[n] = nonce;
  }

  memset (&stats, 0, sizeof (stats)); // Initialize statistics.
}

Drup2Itp::~Drup2Itp () {
  vals -= size_vars;
  delete[] vals;
  for (size_t i = 0; i < size_clauses; i++)
    for (Clause *c = clauses[i], *next; c; c = next)
      next = c->next, delete_clause (c);
  delete[] clauses;
}

/*------------------------------------------------------------------------*/

uint64_t Drup2Itp::reduce_hash (uint64_t hash, uint64_t size) {
  assert (size > 0);
  unsigned shift = 32;
  uint64_t res = hash;
  while ((((uint64_t) 1) << shift) > size) {
    res ^= res >> shift;
    shift >>= 1;
  }
  res &= size - 1;
  assert (res < size);
  return res;
}

// TODO: Not a fan of this function.
void Drup2Itp::enlarge_marks (int idx) {
  assert (0 < idx), assert (idx <= INT_MAX);
  int64_t size = 2;
  while (idx >= size)
    size *= 2;
  assert (size >= marks.size ());
  marks.resize (2 * size);
}

signed char Drup2Itp::marked (int lit) const {
  assert (abs (lit) < marks.size ());
  signed char res = marks[abs (lit)];
  if (lit < 0)
    res = -res;
  return res;
}

void Drup2Itp::mark (int lit) {
  assert (!marked (lit));
  marks[abs (lit)] = (lit > 0) - (lit < 0);
  assert (marked (lit) > 0);
  assert (marked (-lit) < 0);
}

void Drup2Itp::unmark (int lit) {
  assert (abs (lit) < marks.size ());
  marks[abs (lit)] = 0;
  assert (!marked (lit));
}

void Drup2Itp::import_clause (const vector<int> &c) {
  assert (imported_clause.empty ());
  int idx, marks_sz = marks.size ();
  for (int lit : c) {
    idx = abs (lit);
    if (idx >= marks_sz) {
      enlarge_marks (idx);
      marks_sz = marks.size ();
    }
  }
  imported_tautological = false;
  int tmp;
  for (int lit : c) {
    tmp = marked (lit);
    if (tmp < 0)
      imported_tautological = true;
    else if (!tmp) {
      imported_clause.push_back (lit);
      mark (lit);
    }
  }
  for (const auto &lit : c)
    unmark (lit);
}

uint64_t Drup2Itp::compute_hash (const uint64_t id) {
  assert (id > 0);
  unsigned j = id % num_nonces;
  uint64_t tmp = nonces[j] * (uint64_t) id;
  return tmp;
}

Clause **Drup2Itp::find (const uint64_t id) {
  stats.searches++;
  Clause **res, *c;
  const uint64_t hash = compute_hash (id);
  const uint64_t h = reduce_hash (hash, size_clauses);
  for (res = clauses + h; (c = *res); res = &c->next) {
    if (c->hash == hash && c->id == id)
      break;
    stats.collisions++;
  }
  return res;
}

Clause *Drup2Itp::insert (const vector<int> &literals, uint64_t id) {
  stats.insertions++;
  if (num_clauses == size_clauses)
    enlarge_clauses ();
  uint64_t hash = compute_hash (id);
  const uint64_t h = reduce_hash (hash, size_clauses);
  Clause *c = new_clause (literals, id, hash);
  c->next = clauses[h];
  clauses[h] = c;
  return c;
}

/*------------------------------------------------------------------------*/

inline void Drup2Itp::assign (int lit, Clause *reason) {
  assert (!val (lit));
  vals[lit] = 1;
  vals[-lit] = -1;
  int idx = abs (lit);
  lit2trail[idx] = trail.size ();
  trail.push_back (lit);
  reasons[idx] = reason;
  if (reason) {
    int *lits = reason->literals;
    for (unsigned i = 0; i < reason->size && lits[0] != lit; i++) {
      if (lits[i] != lit)
        continue;
      lits[i] = lits[0];
      lits[0] = lit;
    }
    assert (lit == lits[0]);
  }
}

inline void Drup2Itp::assume (int lit) {
  signed char tmp = val (lit);
  if (tmp > 0)
    return;
  assert (!tmp);
  stats.assumptions++;
  last_assumed_trail = trail.size ();
  assign (lit, 0);
}

void Drup2Itp::backtrack (unsigned previously_propagated) {

  assert (previously_propagated <= trail.size ());

  while (trail.size () > previously_propagated) {
    int lit = trail.back ();
    undo_trail_literal (lit);
    trail.pop_back ();
  }

  trail.resize (previously_propagated);
  next_to_propagate = previously_propagated;
  assert (trail.size () == next_to_propagate);
  conflict = 0;
}

/*------------------------------------------------------------------------*/

// This is a standard propagation routine without using blocking literals
// nor without saving the last replacement position.

bool Drup2Itp::propagate (bool core) {
  bool res = true;
  while (res && next_to_propagate < trail.size ()) {
    int lit = trail[next_to_propagate++];
    stats.propagations++;
    assert (val (lit) > 0);
    assert (abs (lit) < size_vars);
    Watches &ws = watches (-lit);
    const auto end = ws.end ();
    auto j = ws.begin (), i = j;
    for (; res && i != end; i++) {
      Watch &w = *j++ = *i;
      const int blit = w.blit;
      assert (blit != -lit);
      if (core && !w.clause->core)
        continue;
      if (w.clause->garbage) {
        assert (!detach_eagerly);
        continue;
      }
      const signed char blit_val = val (blit);
      if (blit_val > 0)
        continue; // blocking literal satisfied
      const unsigned size = w.size;
      if (size == 2) {
        if (blit_val < 0) {
          res = false;
          conflict = w.clause;
        } else
          assign (w.blit, w.clause); // but still sound
      } else {
        assert (size > 2);
        Clause *c = w.clause;
        if (!c->size) {
          j--;
          continue;
        } // skip garbage clauses
        assert (size == c->size);
        int *lits = c->literals;
        int other = lits[0] ^ lits[1] ^ (-lit);
        assert (other != -lit);
        signed char other_val = val (other);
        if (other_val > 0) {
          j[-1].blit = other;
          continue;
        }
        lits[0] = other, lits[1] = -lit;
        unsigned k;
        int replacement = 0;
        signed char replacement_val = -1;
        for (k = 2; k < size; k++)
          if ((replacement_val = val (replacement = lits[k])) >= 0)
            break;
        if (replacement_val >= 0) {
          watches (replacement).push_back (Watch (-lit, c));
          swap (lits[1], lits[k]);
          j--;
        } else if (!other_val)
          assign (other, c);
        else {
          res = false;
          conflict = c;
        }
      }
    }
    while (i != end)
      *j++ = *i++;
    ws.resize (j - ws.begin ());
  }
  return res;
}

void Drup2Itp::detach_clause (Clause *c) {
  assert (c && !c->garbage);
  c->garbage = true;
  if (detach_eagerly) {
    if (c->size > 1)
      unwatch_clause (c);
  } else if (num_watched_garbage * 2 >= num_watched)
    flush_watches ();
  else
    num_watched_garbage += 2;
}

void Drup2Itp::attach_clause (Clause *c) {
  assert (c && c->garbage);
  c->garbage = false;
  if (c->size > 1)
    watch_clause (c);
}

bool Drup2Itp::satisfied (Clause *c) {
  assert (c);
  for (int lit : *c)
    if (val (lit) > 0)
      return true;
  return false;
}

void Drup2Itp::init_vals () {
  assert (0 < max_var && max_var <= INT_MAX);
  size_vars = 2;
  while (max_var >= size_vars)
    size_vars *= 2;
  vals = new signed char[2 * size_vars];
  CaDiCaL::clear_n (vals, 2 * size_vars);
  vals += size_vars;
  assert (max_var < size_vars);
}

void Drup2Itp::init_trail_and_reasons () {
  assert (vals); // should be already initialized
  reasons.clear (), reasons.resize (size_vars, 0);
  const auto &itrail = internal->trail;
  const size_t size = itrail.size ();
  const auto &iunit_clauses = internal->unit_clauses;
  trail.resize (size);
  // TODO: I think it's ok not to clear here.
  lit2trail.clear (), lit2trail.resize (size_vars, 0);
  int lit, idx;
  for (size_t i = 0; i < size; i++) {
    lit = trail[i] = itrail[i], idx = abs (lit);
    assert (!vals[lit] && !vals[-lit]);
    vals[lit] = 1, vals[-lit] = -1;
    lit2trail[idx] = i;
    CaDiCaL::Clause *reason = internal->var (idx).reason;
    if (reason) {
      reasons[idx] = *find (reason->id);
      assert (reasons[idx]);
    } else if (int id = iunit_clauses[internal->vlit (lit)]) {
      reasons[idx] = *find (id);
      assert (reasons[idx]);
    } else {
      assert (0 && "no assumptions at level zero");
    }
    assert (reasons[idx]);
    assert (reasons[idx]->literals[0] == lit);
  }
  next_to_propagate = trail.size ();
  last_assumed_trail = 0;
}

int Drup2Itp::init_data_structures () {
  internal->backtrack ();
  assert (!internal->level);
  assert (external->max_var >= max_var);
  if (watching ())
    reset_watches ();
  if (vals) {
    vals -= size_vars;
    delete[] vals;
    vals = 0;
  }
  max_var = external->max_var;
  if (!max_var)
    return 0;
  // if (marks.size () <= max_var)
  marks.resize (size_vars, 0);
  init_vals ();
  init_trail_and_reasons ();
  init_watches ();
  connect_watches ();
  seen.clear (), seen.resize (size_vars, 0);
  return 1;
}

void Drup2Itp::apply_RUP (Clause *c, unsigned &trail_sz) {
  assert (c);
  shrink_trail (trail_sz);
  top_root_trail = trail.size () - 1;
  for (int lit : *c)
    assume (-lit);
  if (propagate ()) {
    assert (next_to_propagate >= c->size);
    next_to_propagate -= c->size;
    if (propagate ()) {
      CaDiCaL::fatal_message_start ();
      fputs ("RUP failed for proof core lemma: ", stderr);
      for (const auto &lit : *c)
        fprintf (stderr, "%d ", lit);
      fputc ('0', stderr);
      CaDiCaL::fatal_message_end ();
    }
  }
  analyze_core ();
  backtrack (trail_sz);
}

bool Drup2Itp::is_on_trail (Clause *c) {
  assert (c);
  int lit = c->literals[0];
  return val (lit) > 0 && (reasons[abs (lit)]->id == c->id);
}

void Drup2Itp::undo_trail_literal (int lit) {
  unsigned idx = abs (lit);
  assert (idx < reasons.size ());
  reasons[idx] = 0;
  assert (val (lit) > 0);
  assert (val (-lit) < 0);
  vals[lit] = vals[-lit] = 0;
  lit2trail[idx] = 0; // or -1 ? it shouldn't be accessed anyway...
}

void Drup2Itp::undo_trail_core (Clause *c, unsigned &trail_sz) {
#ifndef NDEBUG
  assert (trail_sz > 0);
  assert (trail_sz <= trail.size ());
  assert (c && is_on_trail (c));
#endif

  int clit = c->literals[0];

#ifndef NDEBUG
  assert (reasons[abs (clit)] == c);
  assert (val (clit) > 0);
#endif

  while (trail[--trail_sz] != clit) {
    assert (trail_sz > 0);
    int l = trail[trail_sz];

    Clause *r = reasons[abs (l)];
    assert (r && r->literals[0] == l);

    undo_trail_literal (l);

    if (r->core)
      for (unsigned j = 1; j < r->size; j++) {
        Clause *cr = reasons[abs (r->literals[j])];
        assert (cr);
        cr->core = true;
      }
  }

  assert (clit == trail[trail_sz]);
  undo_trail_literal (clit);
}

void Drup2Itp::shrink_trail (unsigned trail_sz) {
  assert (trail_sz <= trail.size ());
  trail.resize (trail_sz);
  next_to_propagate = trail_sz;
}

void Drup2Itp::analyze_core_literal (int lit) {
  int idx = abs (lit), trail_idx = lit2trail[idx];
  assert (idx < size_vars);
  if (trail_idx > last_assumed_trail) {
    seen[idx] = true;
  } else if (trail_idx <= top_root_trail) {
    Clause *reason = reasons[idx];
    assert (reason);
    reason->core = true;
  }
}

void Drup2Itp::analyze_core () {
  assert (conflict);
  conflict->core = true;

  for (int lit : *conflict)
    analyze_core_literal (lit);

  for (int i = trail.size () - 1; i > last_assumed_trail; i--) {
    int lit = trail[i], idx = abs (lit);
    assert (idx < size_vars);
    if (!seen[idx])
      continue;

    seen[idx] = false;

    Clause *c = reasons[idx];
    assert (c);
    c->core = true;

#ifndef NDEBUG
    assert (reasons[abs (c->literals[0])] == c);
    assert (val (c->literals[0]) > 0);
    assert (c->literals[0] == lit);
#endif

    for (unsigned j = 1; j < c->size; j++)
      analyze_core_literal (c->literals[j]);
  }
}

void Drup2Itp::mark_core_trail_antecedents () {
  for (int i = trail.size () - 1; i >= 0; i--) {
    int lit = trail[i];
    assert (abs (lit) < size_vars);
    Clause *reason = reasons[abs (lit)];
    assert (reason);
    if (reason->core) {
      assert (reason->literals[0] == lit);
      for (int lit : *reason) {
        assert (abs (lit) < size_vars);
        Clause *cr = reasons[abs (lit)];
        assert (cr);
        cr->core = true;
      }
      next_to_propagate = i;
    }
  }
}

void Drup2Itp::mark_top_conflict () {
  switch (conclusion) {
  case ConclusionType::CONFLICT: {
    if (top_conflict) {
      top_conflict->core = true;
      for (int lit : *top_conflict) {
        assert (abs (lit) < size_vars);
        if (Clause *c = reasons[abs (lit)])
          c->core = true;
      }
    }
  } break;
  case ConclusionType::ASSUMPTIONS: {
    if (size_clauses)
      for (int lit : assumptions)
        if (external->failed (lit)) {
          assert (abs (lit) < size_vars);
          Clause *c = reasons[abs (lit)];
          if (c)
            c->core = true;
        }
  } break;
  case ConclusionType::CONSTRAINT: {
    if (size_clauses)
      for (int lit : constraint) {
        assert (abs (lit) < size_vars);
        Clause *c = reasons[abs (lit)];
        if (c)
          c->core = true;
      }
  } break;
  default:
    assert (false && "should not reach here");
  }
}

bool Drup2Itp::trim () {

  stats.trims++;
  assert (!empty_original_clause);
  if (!init_data_structures ())
    return true;

  mark_top_conflict ();

  // // 'trail_sz' is used for lazy shrinking of the trail.
  unsigned trail_sz = trail.size ();

  // Main trimming loop
  for (int i = proof.size () - 1; i >= 0; i--) {
    Clause *c = proof[i];

    if (c->garbage) {
      attach_clause (c);
      continue;
    }

    if (is_on_trail (c))
      undo_trail_core (c, trail_sz);

    detach_clause (c);

    if (c->core)
      apply_RUP (c, trail_sz);
  }

  shrink_trail (trail_sz);
  mark_core_trail_antecedents ();

  return true;
}

bool Drup2Itp::trim (CaDiCaL::ClauseIterator &it, bool undo) {

  if (empty_original_clause)
    return true;

  if (!trim ())
    return false;

  traverse_core (it);

  if (undo) {
    // For application where only core is needed
    for (Clause *c : proof) {
      c->garbage = !c->garbage;
      c->core = false;
    }
    if (!empty_original_clause)
      restore_trail ();
  }
  return true;
}

void Drup2Itp::restore_trail () {
  for (uint64_t i = 0; i < size_clauses; i++)
    for (Clause *c = clauses[i]; c; c = c->next) {
      if (c->size != 1)
        continue;
      int unit = c->literals[0];
      if (val (unit))
        continue;
      assign (unit, c);
      propagate ();
    }
}

static bool starts_with_suffix (const char *str, const char *suffix) {
    string str_str(str);
    string suffix_str(suffix);
    if (str_str.length() < suffix_str.length())
        return false;
    return str_str.compare(0, suffix_str.length(), suffix_str) == 0;
}

bool Drup2Itp::supported_option (const char *arg) const {
  if (starts_with_suffix (arg, "ilbassumptions"))
    return false;
  if (starts_with_suffix (arg, "probe"))
    return false;
  if (starts_with_suffix (arg, "compact"))
    return false;
  if (starts_with_suffix (arg, "block"))
    return false;
  if (starts_with_suffix (arg, "cover"))
    return false;
  if (starts_with_suffix (arg, "probe"))
    return false;
  return true;
}

void Drup2Itp::append (uint64_t id, const vector<int> &literals,
                       bool deletion) {
  stats.added++;
  Clause *c = size_clauses ? *find (id) : 0;
  if (deletion) {
    stats.deleted++;
    if (c) {
      assert (c->size == literals.size () && c->id == id);
      // assert (!c->garbage); // TODO: apparently this can gappen... :(
      // need to investigate this.
      c->garbage = true;
      proof.push_back (c);
    } else {
      CaDiCaL::fatal_message_start ();
      fputs ("deleted clause not in proof:\n", stderr);
      for (const auto &lit : literals)
        fprintf (stderr, "%d ", lit);
      fputc ('0', stderr);
      CaDiCaL::fatal_message_end ();
    }
  } else {
    assert (!c);
    stats.derived++;
    c = insert (literals, id);
    proof.push_back (c);
    inconsistent |= !c->size;
  }
}

void Drup2Itp::traverse_core (CaDiCaL::ClauseIterator &it) {
  vector<int> clause;
  for (uint64_t i = 0; i < size_clauses; i++)
    for (Clause *c = clauses[i]; c; c = c->next) {
      if (!c->original || !c->core)
        continue;
      for (int lit : *c)
        clause.push_back (lit);
      if (!it.clause (clause))
        return;
      clause.clear ();
    }
  for (int lit : assumptions)
    if (external->failed (lit)) {
      clause.push_back (lit);
      if (!it.clause (clause))
        return;
      clause.clear ();
    }
  if (conclusion == ConclusionType::CONSTRAINT) {
    for (int lit : constraint)
      clause.push_back (lit);
    if (!it.clause (clause))
      return;
    clause.clear ();
  }
}

Watches &Drup2Itp::watches (int lit) {
  return (Watches &) (wtab[vlit (lit)]);
}

void Drup2Itp::sort_watch (Clause *c) {
  assert (c);
  if (c->size <= 2)
    return;
  WatchSort sorter (lit2trail, vals);
  int *lits = c->literals;
  const int size = c->size;
  for (int i = 0; i < 2; i++)
    for (int j = i + 1; j < size; j++)
      if (!sorter (lits[i], lits[j]))
        swap (lits[i], lits[j]);
}

void Drup2Itp::init_watches () {
  assert (wtab.empty ());
  wtab.resize (2 * (size_vars));
}

void Drup2Itp::clear_watches () {
  for (int idx = 1; idx <= max_var; idx++) {
    watches (idx).clear ();
    watches (-idx).clear ();
  }
}

void Drup2Itp::reset_watches () {
  assert (!wtab.empty ());
  CaDiCaL::erase_vector (wtab);
}

// This can be quite costly since lots of memory is accessed in a rather
// random fashion, and thus we optionally profile it.

void Drup2Itp::connect_watches (bool core_only) {
  START (connect);
  assert (watching () && vals);

  // First connect binary clauses.
  //
  for (uint64_t i = 0; i < size_clauses; i++)
    for (Clause *c = clauses[i]; c; c = c->next) {
      if (core_only && !c->core)
        continue;
      if (c->garbage || c->size != 2)
        continue;
      watch_clause (c);
    }

  // Then connect non-binary clauses.
  //
  for (uint64_t i = 0; i < size_clauses; i++)
    for (Clause *c = clauses[i]; c; c = c->next) {
      if (core_only && !c->core)
        continue;
      if (c->garbage || c->size <= 2)
        continue;
      watch_clause (c);
    }

  STOP (connect);
}

void Drup2Itp::flush_watches (int lit, Watches &saved) {
  assert (saved.empty ());
  Watches &ws = watches (lit);
  const const_watch_iterator end = ws.end ();
  watch_iterator j = ws.begin ();
  const_watch_iterator i;
  for (i = j; i != end; i++) {
    Watch w = *i;
    Clause *c = w.clause;
    if (c->garbage) {
      num_watched--;
      continue;
    }
    w.size = c->size;
    const int new_blit_pos = (c->literals[0] == lit);
    assert (c->literals[!new_blit_pos] == lit); /*FW1*/
    w.blit = c->literals[new_blit_pos];
    if (w.binary ())
      *j++ = w;
    else
      saved.push_back (w);
  }
  ws.resize (j - ws.begin ());
  for (const auto &w : saved)
    ws.push_back (w);
  saved.clear ();
  CaDiCaL::shrink_vector (ws);
}

void Drup2Itp::flush_watches () {
  CaDiCaL::Range vars (max_var);
  if (watching ()) {
    Watches tmp;
    for (auto idx : vars)
      flush_watches (idx, tmp), flush_watches (-idx, tmp);
  }
  num_watched_garbage = 0;
}

bool Drup2Itp::watching () const { return !wtab.empty (); }

// TODO: inline it
void Drup2Itp::watch_literal (int lit, int blit, Clause *c) {
  assert (lit != blit);
  Watches &ws = watches (lit);
  ws.push_back (Watch (blit, c));
}

void Drup2Itp::watch_clause (Clause *c) {
  assert (c);
  // TODO: Find a better solution for this.
  sort_watch (c);
  const int l0 = c->literals[0];
  const int l1 = c->literals[1];
  watch_literal (l0, l1, c);
  watch_literal (l1, l0, c);
  num_watched += 2;
}

void Drup2Itp::unwatch_clause (Clause *c) {
  assert (c);
  const int l0 = c->literals[0];
  const int l1 = c->literals[1];
  remove_watch (watches (l0), c);
  remove_watch (watches (l1), c);
  num_watched -= 2;
}

/*------------------------------------------------------------------------*/

void Drup2Itp::connect_internal (Internal *i) {
  assert (i);
  internal = i;
  external = i->external;
}

void Drup2Itp::add_original_clause (uint64_t id, bool redundant,
                                    const vector<int> &c, bool restore) {
  START (checking);
  stats.added++;
  stats.original++;
  if (c.empty ()) {
    Clause *oc = insert (c, id);
    oc->original = true;
    inconsistent = true;
    empty_original_clause = true;
  } else {
    import_clause (c);
    if (!imported_tautological) {
      Clause *oc = insert (imported_clause, id);
      oc->original = true;
    }
    imported_clause.clear ();
  }
  STOP (checking);
}

void Drup2Itp::add_derived_clause (uint64_t id, bool redundant,
                                   const vector<int> &c,
                                   const vector<uint64_t> &chain) {
  if (inconsistent)
    return;
  START (checking);
  if (c.empty ()) {
    insert (c, id);
    inconsistent = true;
    // TODO: It's unclear how the current tracer API can help provide the
    // necessary information without having to request antecedencts. This
    // the only place where proof chain is needed for trimming.
    assert (chain.size ());
    top_conflict = *find (chain.back ());
  } else {
    import_clause (c);
    if (!imported_tautological)
      append (id, imported_clause, false /*addition*/);
    imported_clause.clear ();
  }
  STOP (checking);
}

void Drup2Itp::add_assumption_clause (uint64_t id, const vector<int> &c,
                                      const vector<uint64_t> &) {
  if (c.size () > 1) {
    import_clause (c);
    if (!imported_tautological) {
      append (id, imported_clause, false /*addition*/);
      append (id, imported_clause, true /*deletion*/);
      proof.back ()->core = true;
    }
    imported_clause.clear ();
  } else {
    stats.added++;
    Clause *ac = insert (c, id);
    ac->core = true;
  }
}

void Drup2Itp::delete_clause (uint64_t id, bool redundant,
                              const vector<int> &c) {
  if (inconsistent)
    return;
  START (checking);
  import_clause (c);
  if (!imported_tautological) {
    append (id, imported_clause, true /*deletion*/);
    int *lits = proof.back ()->literals, size = proof.back ()->size;
    for (int i = 0; i < size; i++)
      if (external->fixed (lits[i]) < 0)
        swap (lits[i], lits[--size]);
  }
  imported_clause.clear ();
  STOP (checking);
}

void Drup2Itp::add_assumption (int lit) { assumptions.push_back (lit); }

void Drup2Itp::add_constraint (const vector<int> &c) {
  // If the user adds a constraint while there is already one,
  // the previous one is discarded. It's better if discarding the previous
  // was done explicitly through the tracer API however.
  // assert (constraint.empty ());
  constraint.clear ();
  for (int lit : c)
    constraint.push_back (lit);
}

void Drup2Itp::reset_assumptions () {
  assumptions.clear ();
  constraint.clear ();
}

void Drup2Itp::conclude_unsat (ConclusionType c, const vector<uint64_t> &) {
  conclusion = c;
}

void Drup2Itp::print_stats () {
  if (!stats.added && !stats.deleted)
    return;

  SECTION ("drup2itp statistics");

  MSG ("trims:           %15" PRId64 "", stats.trims);
  MSG ("assumptions:     %15" PRId64 "   %10.2f    per trim",
       stats.assumptions,
       CaDiCaL::relative (stats.assumptions, stats.trims));
  MSG ("propagations:    %15" PRId64 "   %10.2f    per trim",
       stats.propagations,
       CaDiCaL::relative (stats.propagations, stats.trims));
  MSG ("original:        %15" PRId64 "   %10.2f %%  of all clauses",
       stats.original, CaDiCaL::percent (stats.original, stats.added));
  MSG ("derived:         %15" PRId64 "   %10.2f %%  of all clauses",
       stats.derived, CaDiCaL::percent (stats.derived, stats.added));
  MSG ("deleted:         %15" PRId64 "   %10.2f %%  of all clauses",
       stats.deleted, CaDiCaL::percent (stats.deleted, stats.added));
  MSG ("insertions:      %15" PRId64 "   %10.2f %%  of all clauses",
       stats.insertions, CaDiCaL::percent (stats.insertions, stats.added));
  MSG ("collisions:      %15" PRId64 "   %10.2f    per search",
       stats.collisions,
       CaDiCaL::relative (stats.collisions, stats.searches));
  MSG ("searches:        %15" PRId64 "", stats.searches);
  MSG ("units:           %15" PRId64 "", stats.units);
}

void Drup2Itp::dump (const char *type) {
  if (strcmp (type, "proof") == 0) {
    fprintf (stderr, "DUMP PROOF TAIL\n");
    for (int i = proof.size () - 1; i >= 0; i--) {
      Clause *c = proof[i];
      fprintf (stderr, "[%lu] [%s] [ ", c->id, c->garbage ? "d" : "a");
      for (int lit : *c)
        fprintf (stderr, "%d ", lit);
      fprintf (stderr, "]\n");
    }
    fprintf (stderr, "DUMP PROOF HEAD\n");
  } else if (strcmp (type, "core") == 0) {
    fprintf (stderr, "DUMP CORE START\n");
    for (uint64_t i = 0; i < size_clauses; i++)
      for (Clause *c = clauses[i]; c; c = c->next) {
        if (!c->core)
          continue;
        fprintf (stderr, "[%s] id:[%lu] c:[ ",
                 c->original ? "orig" : "deri", c->id);
        for (int lit : *c)
          fprintf (stderr, "%d ", lit);
        fprintf (stderr, "]\n");
      }
    fprintf (stderr, "DUMP CORE END\n");
  } else if (strcmp (type, "clauses") == 0) {
    fprintf (stderr, "DUMP CLAUSES START\n");
    for (uint64_t i = 0; i < size_clauses; i++)
      for (Clause *c = clauses[i]; c; c = c->next) {
        fprintf (stderr, "[%s] [%s] [%lu] [ ",
                 c->original ? "orig" : "deri",
                 c->garbage ? "garb" : "activ", c->id);
        for (int lit : *c)
          fprintf (stderr, "%d ", lit);
        fprintf (stderr, "]\n");
      }
    fprintf (stderr, "DUMP CLAUSES END\n");
  } else if (strcmp (type, "active") == 0) {
    fprintf (stderr, "DUMP ACTIVE CLAUSES START\n");
    for (uint64_t i = 0; i < size_clauses; i++)
      for (Clause *c = clauses[i]; c; c = c->next) {
        if (c->garbage)
          continue;
        fprintf (stderr, "[%s] [%lu] [ ", c->original ? "orig" : "deri",
                 c->id);
        for (int lit : *c)
          fprintf (stderr, "%d ", lit);
        fprintf (stderr, "]\n");
      }
    fprintf (stderr, "DUMP ACTIVE CLAUSES END\n");
  } else if (strcmp (type, "trail") == 0) {
    fprintf (stderr, "DUMP TRAIL TAIL\n");
    for (int i = trail.size () - 1; i >= 0; i--) {
      int lit = trail[i];
      fprintf (stderr, "%d <- ", lit);
      Clause *c = reasons[abs (lit)];
      if (!c)
        fprintf (stderr, "[0] [0]\n");
      else {
        fprintf (stderr, "[%lu] [ ", c->id);
        for (int lit : *c)
          fprintf (stderr, "%d ", lit);
        fprintf (stderr, "]\n");
      }
    }
    fprintf (stderr, "DUMP TRAIL HEAD\n");
  } else
    assert (0);
}

} // namespace CaDiCaLDRUP2Itp
