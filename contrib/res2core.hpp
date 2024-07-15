// Created by Basel Khouri 2024

#ifndef _res2core_hpp_INCLUDED
#define _res2core_hpp_INCLUDED

#include "cadical.hpp"
#include "internal.hpp"
#include "tracer.hpp"

#include <iostream>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

namespace CaDiCaLRes2Core {

using namespace std;
using CaDiCaL::ConclusionType;
using CaDiCaL::Internal;
using CaDiCaL::External;
using CaDiCaL::Solver;


struct Clause {
  Clause *next;
  uint64_t hash;
  uint64_t id;
  bool core;
  bool original;
  unsigned size;
  int literals[1];
  typedef int *literal_iterator;
  typedef const int *const_literal_iterator;
  literal_iterator begin () { return literals; }
  literal_iterator end () { return literals + size; }
  const_literal_iterator begin () const { return literals; }
  const_literal_iterator end () const { return literals + size; }
};

class Res2Core : public CaDiCaL::StatTracer {
  Internal *internal;
  External *external;
  bool inconsistent;
  vector<Clause *> proof;               // stack of learnt lemmas
  vector<vector<uint64_t>> chains;      // stack of chains
  vector<signed char> marks;
  vector<int> imported_clause;          // last imported clause
  bool imported_tautological;           // last imported clause is tautological
  uint64_t num_clauses;                 // number of clauses
  uint64_t size_clauses;                // size of clause hash table
  Clause **clauses;                     // hash table of clauses
  static const unsigned num_nonces = 4;
  uint64_t nonces[num_nonces];          // random numbers for hashing
  void enlarge_marks (int); // Dynamicly managed
  signed char marked (int lit) const;
  void mark (int);
  void unmark (int);
  void import_clause (const vector<int> &);
  uint64_t compute_hash (uint64_t);
  static uint64_t reduce_hash (uint64_t, uint64_t);
  void enlarge_clauses ();
  Clause *insert (const vector<int> &, uint64_t);
  Clause **find (const uint64_t);
  Clause *new_clause (const vector<int> &, uint64_t, uint64_t);
  void delete_clause (Clause *);

  struct {
    int64_t added;        // number of added clauses
    int64_t original;     // number of added original clauses
    int64_t derived;      // number of added derived clauses
    int64_t deleted;      // number of deleted clauses
    int64_t assumptions;  // number of assumed literals
    int64_t propagations; // number of propagated literals
    int64_t insertions;   // number of clauses added to hash table
    int64_t collisions;   // number of hash collisions in 'find'
    int64_t searches;     // number of searched clauses in 'find'
    int64_t trims;        // number of trims
    int64_t units;
  } stats;


public:
  Res2Core ();
  ~Res2Core ();
  void connect_internal (Internal *i) override;
  void add_original_clause (uint64_t, bool, const vector<int> &,
                            bool) override;
  void add_derived_clause (uint64_t, bool, const vector<int> &,
                           const vector<uint64_t> &) override;
  // void delete_clause (uint64_t, bool, const vector<int> &) override;
  // void weaken_minus (uint64_t, const vector<int> &) override;
  // void strengthen (uint64_t) override;
  // void report_status (int, uint64_t) override;
  // void solve_query () override;
  // void add_assumption (int) override;
  // void add_constraint (const vector<int> &) override;
  // void reset_assumptions () override;
  void add_assumption_clause (uint64_t, const vector<int> &,
                              const vector<uint64_t> &) override;
  // void conclude_unsat (ConclusionType, const vector<uint64_t> &) override;
  // void conclude_sat (const vector<int> &) override;
  void print_stats () override;
  void trim (CaDiCaL::ClauseIterator &, bool undo = true);
  bool supported_option (const char *) const;
};

} // namespace CaDiCaLRes2Core

#endif
