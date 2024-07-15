// Created by Basel Khouri 2024

#include "res2core.hpp"
#include "random.hpp"
#include "util.hpp"

extern "C" {
#include <assert.h>
}

namespace CaDiCaLRes2Core {

/*------------------------------------------------------------------------*/

Clause *Res2Core::new_clause (const vector<int> &literals, uint64_t id,
                              uint64_t hash) {
  const size_t size = literals.size ();
  assert (size <= UINT_MAX);
  const int off = size ? 1 : 0;
  const size_t bytes = sizeof (Clause) + (size - off) * sizeof (int);
  Clause *res = (Clause *) new char[bytes];
  res->next = 0;
  res->hash = hash;
  res->id = id;
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

void Res2Core::delete_clause (Clause *c) {
  assert (num_clauses);
  num_clauses--;
  delete[] (char *) c;
}

void Res2Core::enlarge_clauses () {
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

Res2Core::Res2Core ()
    : internal (0), inconsistent (false),
    imported_tautological (false), num_clauses (0),
    size_clauses (0), clauses (0) {
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

Res2Core::~Res2Core () {
  for (size_t i = 0; i < size_clauses; i++)
    for (Clause *c = clauses[i], *next; c; c = next)
      next = c->next, delete_clause (c);
  delete[] clauses;
}

/*------------------------------------------------------------------------*/

uint64_t Res2Core::reduce_hash (uint64_t hash, uint64_t size) {
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
void Res2Core::enlarge_marks (int idx) {
  assert (0 < idx), assert (idx <= INT_MAX);
  unsigned size = 2;
  while (idx >= size)
    size *= 2;
  assert (size >= marks.size ());
  marks.resize (2 * size);
}

signed char Res2Core::marked (int lit) const {
  assert (abs (lit) < marks.size ());
  signed char res = marks[abs (lit)];
  if (lit < 0)
    res = -res;
  return res;
}

void Res2Core::mark (int lit) {
  assert (!marked (lit));
  marks[abs (lit)] = (lit > 0) - (lit < 0);
  assert (marked (lit) > 0);
  assert (marked (-lit) < 0);
}

void Res2Core::unmark (int lit) {
  assert (abs (lit) < marks.size ());
  marks[abs (lit)] = 0;
  assert (!marked (lit));
}

void Res2Core::import_clause (const vector<int> &c) {
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

uint64_t Res2Core::compute_hash (const uint64_t id) {
  assert (id > 0);
  unsigned j = id % num_nonces;
  uint64_t tmp = nonces[j] * (uint64_t) id;
  return tmp;
}

Clause **Res2Core::find (const uint64_t id) {
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

Clause *Res2Core::insert (const vector<int> &literals, uint64_t id) {
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

static bool starts_with_suffix (const char *str, const char *suffix) {
    string str_str(str);
    string suffix_str(suffix);
    if (str_str.length() < suffix_str.length())
        return false;
    return str_str.compare(0, suffix_str.length(), suffix_str) == 0;
}

bool Res2Core::supported_option (const char *arg) const {
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
  return true;
}
/*------------------------------------------------------------------------*/

void Res2Core::connect_internal (Internal *i) {
  assert (i);
  internal = i;
  external = i->external;
}

void Res2Core::add_original_clause (uint64_t id, bool /*redundant*/,
                                    const vector<int> &c, bool /*restore*/) {
  stats.added++;
  stats.original++;
  import_clause (c);
  if (!imported_tautological)
    insert (imported_clause, id)->original = true;
  imported_clause.clear ();
}

void Res2Core::add_derived_clause (uint64_t id, bool /*redundant*/,
                                   const vector<int> &c,
                                   const vector<uint64_t> &chain) {
  if (inconsistent)
    return;
  import_clause (c);
  if (!imported_tautological) {
    Clause *lemma = insert (imported_clause, id);
    proof.push_back (lemma);
    chains.push_back (chain);
    assert (chains.size () == proof.size ());
    if (c.empty ())
      inconsistent = true;
  }
  imported_clause.clear ();
}

static bool notify_clause (CaDiCaL::ClauseIterator &it, CaDiCaLRes2Core::Clause *lemma, vector<int> &clause) {
  assert (lemma && clause.empty ());
  for (int lit : *lemma)
      clause.push_back (lit);
  if (!it.clause (clause))
    return false;
  clause.clear ();
  return true;
}

void Res2Core::trim (CaDiCaL::ClauseIterator &it, bool undo) {
  assert (chains.size () == proof.size ());
  assert (proof.size () && !proof.back ()->size);
  proof.back ()->core = true;
  vector<int> clause;
  for (int i = proof.size () - 1; i >= 0; i--) {
    Clause *lemma = proof[i];
    if (!lemma->core)
      continue;
    for (auto id : chains[i]) {
      Clause *antecedent = *find (id);
      assert (antecedent);
      antecedent->core = true;
      if (antecedent->original)
        notify_clause (it, *find (id), clause);
    }
  }

  if (undo)
    for (uint64_t i = 0; i < size_clauses; i++)
      for (Clause *c = clauses[i]; c; c = c->next)
        c->core = false;
}

void Res2Core::add_assumption_clause (uint64_t id, const vector<int> &c,
                                      const vector<uint64_t> &chain) {
  add_derived_clause (id, true, c, chain);
}

void Res2Core::print_stats () {
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

} // namespace CaDiCaLRes2Core
