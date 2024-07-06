#ifndef _drupper_hpp_INCLUDED
#define _drupper_hpp_INCLUDED

namespace CaDiCaL {

/*-----------------------------------------------------------------------------------

  The code implements the algorithm introduced in "DRUPing For Interpolant",
  a paper by Arie Gurfinkel and Yakir Vizel. It allows in-memory DRUP-based
  proof validation, core and interpolants enabled by 'opts.drup'.
  This implementation was created by Basel Khouri as part of a Bachelor project
  at the Technion under the supervision of Dr. Yakir Vizel.

  Notes:
    - Allowing other proof observers/checkers in parallel is not supported.
      During validation/trimming procedure, drupper can delete or revive
      clauses that other Internal::Proof observers aren't aware of. As a result,
      enabling such observers and checkers in parallel might trigger errors.

    - Chronological backtracking enabled by 'opts.chrono' is incompatible yet.
      The combination of chronological backtracking with the algorithm is
      challenging since invariants classically considered crucial to CDCL cease to
      hold. In its current implementation, the algorithm relies on the level order
      invariant which ensures the literals are ordered on the assignment trail in
      ascending order with respect to their decision level. This invariant is
      violated. In the interest of compatibility with chronological backtracking,
      adjustments to the implementation will be considered in the future.

-----------------------------------------------------------------------------------*/

enum DCVariant { CLAUSE = 0, LITERALS = 1 };

// A deallocated Clause object will have a DrupperClause object counterpart
// maintaining its literals and color range in a single std::vector<int>.
// For a clause of size N, we maintain a vector of size N+1 s.t.:
// - literals are kept in entries 0, ..., N-1.
// - range is encoded to an integer and is in entry [N].
//
// This iterator excludes the last entry, which is color range code integer.
class DrupperClauseIterator {
private:
  const vector<int> &m_clause;
  size_t m_index;

public:
  explicit DrupperClauseIterator (const vector<int> &, size_t);
  int operator* () const;
  DrupperClauseIterator &operator++ ();
  DrupperClauseIterator &operator+ (int);
  bool operator!= (const DrupperClauseIterator &other) const;
};

class DrupperClause {
  bool variant : 1;

public:
  bool deleted : 1;
  unsigned revive_at : 30;

private:
  union {
    Clause *counterpart;
    vector<int> *literals;
  };
  const vector<int> &lits () const;

public:
  DrupperClause (vector<int> c, int code, bool deletion = false);
  DrupperClause (Clause *c, bool deletion = false);
  ~DrupperClause ();
  DCVariant variant_type () const;
  void destroy_variant ();
  void set_variant (Clause *);
  Clause *flip_variant (int);
  Clause *clause ();
  int color_range_code () const;
  int size () const;
  DrupperClauseIterator lits_begin () const;
  DrupperClauseIterator lits_end () const;
};

struct DrupperData {
  bool core : 1;    // clause has been found to be core since last 'trim'.
  bool lemma : 1;   // if core = true, this is an implied core lemma.
  unsigned idx:30;  // reverse mapping used by drupper.
  DrupperData () : core (false), lemma (false), idx (0) {}
};

class LiteralSort {
  Internal *internal;

public:
  LiteralSort (Internal *i);
  bool operator() (int x, int y) const;
};

class ColorRange {
  unsigned m_min : 16, m_max : 16;

public:
  ColorRange ();
  ColorRange (const unsigned);
  bool undef () const;
  void reset ();
  bool singleton () const;
  void join (const unsigned np);
  void join (const ColorRange &o);
  unsigned min () const;
  unsigned max () const;
  bool operator== (const ColorRange &r);
  bool operator!= (const ColorRange &r);
  void operator= (int);
  int code () const;
};

struct lock_scope {
  bool &key;
  lock_scope (bool &key_) : key (key_) {
    assert (!key_);
    key = true;
  };
  ~lock_scope () { key = false; }
};

template <class T> struct save_scope {
  T &key;
  T initial;
  save_scope (T &key_) : key (key_), initial (key_){};
  save_scope (T &key_, T val_within_scope) : key (key_), initial (key_) {
    key = val_within_scope;
  };
  ~save_scope () { key = initial; };
};

class Drupper {

  Internal *internal;

  // stack of clausal proof
  //
  vector<DrupperClause *> proof;

  unordered_map<Clause *, DrupperData> drup_db;

  Clause *new_redundant_clause (const vector<int> &);
  Clause *new_redundant_clause (const DrupperClause *);
  // to keep up with internal->stats
  void mark_garbage (Clause *);
  void mark_active (Clause *);
  Clause *new_unit_clause (const int, bool);
  void delete_garbage_unit_clauses ();
  vector<Clause *> unit_clauses;

  Clause *failed_constraint, *final_conflict;
  bool isolated, in_action, overconstrained;
  vector<vector<int>> failing_assumptions;

  bool clauses_are_identical (Clause *, const vector<int> &) const;
  void append_lemma (DrupperClause *);
  void revive_clause (const int);
  void stagnate_clause (Clause *);
  void reactivate_fixed (int);
  void reactivate (Clause *);
  bool satisfied (Clause *c);

  void shrink_internal_trail (const unsigned);
  void clean_conflict ();

  void undo_trail_literal (const int);
  void undo_trail_core (Clause *, unsigned &);
  bool is_on_trail (Clause *) const;

  bool lemma (Clause *) const;
  void lemma (Clause *, bool);
  void core (Clause *, bool);
  unsigned idx (Clause *) const;
  void idx (Clause *, unsigned);
  void erase (Clause *);

  void mark_conflict_lit (const int);
  void mark_conflict ();

  void assume_negation (Clause *);
  bool propagate_conflict ();
  bool reverse_unit_propagation (Clause *);
  bool got_value_by_propagation (int) const;
  void conflict_analysis_core ();

  void mark_core_trail_antecedents ();
  void unmark_core ();
  void restore_trail (bool initial_data_base = false);
  void restore_proof_garbage_marks ();

  void check_environment () const;
  void dump_clauses (bool active = false);
  void dump_clause (const Clause *) const;
  void dump_clause (const DrupperClause *) const;
  void dump_clause (const vector<int> &) const;
  void dump_proof ();
  void dump_trail () const;

  void trim_ ();
  void prefer_core_watches (const int);
  bool traverse_core (ClauseIterator &);
  bool traverse_core (ClauseIterator &) const;

  // Interpolation
  //
  unordered_map<uint64_t, ColorRange> clause_ranges;
  //TODO: use a std::vector instaed?
  unordered_map<int, ColorRange> variable_ranges;
  vector<int> unit_ids;
  ColorRange improted_range;
  unsigned max_color : 16;

  ColorRange& range(int);
  void assign_range (Clause *, ColorRange &);
  void assign_range (const vector<int> &);
  void assign_range (int);


  bool unit (Clause *);
  bool shared (Clause *);
  bool color_ordered_propagate (bool core = false);
  bool propagate (bool core = false);
  Clause *recursively_colorize (Clause *, ResolutionIterator &);
  ChainDerivation colorize (Clause *, int, vector<int> &,
                 ColorRange &, ResolutionIterator &);
  bool skip_derivation (Clause *);
  void optimize_proof (vector<Clause *> &);
  void label_initial (ResolutionIterator &, int &, ChainDerivation &);
  void label_final (ResolutionIterator &, Clause *);
  void label_final_assumptions (ResolutionIterator &);
  void replay (ResolutionIterator &);

  // helpers
  //
  void append_chain_anchor (ChainDerivation &, Clause *);
  void append_chain_anchor (ChainDerivation &, int);
  void append_chain_antecedent (ChainDerivation &, Clause *, int);
  void append_chain_antecedent (ChainDerivation &, int);
  void notify_proof_iterator (ResolutionIterator &, const ChainDerivation &, Clause *);
  void notify_proof_iterator (ResolutionIterator &, const ChainDerivation &, int);

  class ReplayAbort : public std::exception {};

  struct {

    int64_t trims = 0;   // number of trim calls
    int64_t derived = 0; // number of added derived clauses
    int64_t deleted = 0; // number of deleted clauses
    int64_t revived = 0; // number of revived clauses
    int64_t units = 0;   // number of unit clauses allcoated

    typedef struct {
      int64_t clauses = 0, lemmas = 0, variables = 0;
    } core_stats;

    core_stats core;               // core statistics in current trim
    vector<core_stats> core_phase; // core statistics per trim phase

  void save_core_phase () {
    core_phase.push_back ({core.clauses, core.lemmas, core.variables});
  }

  } stats;

  bool setup_internal_options ();

  struct Settings {

    bool core_units : 1;        // mark trail reason units as core
    bool check_core : 1;        // assert the set of core literals is unsat (under
                                // debug mode only)
    bool incremental : 1;       // clean core marks after trim
    bool dump : 1;              // dump original extracted core as a cnf file
    bool ordered_propagate;     // replace the replayed proof with the new
                                // optimized proof
    bool optimize_proof : 1;
    bool report : 1;            // report 'm', 'M'

    Settings () { // default
      core_units = false;
      check_core = true;
      incremental = true;
      dump = true;
      ordered_propagate = false;
      optimize_proof = false;
      report = false;
    }

  } settings;

public:
  Drupper (Internal *);
  ~Drupper ();

  void set (const char *, bool val = true);

  void add_derived_clause (Clause *);
  void add_derived_unit_clause (const int, bool original = false);
  void add_derived_empty_clause ();
  void add_falsified_original_clause (const vector<int> &, bool);
  void clear_failing_assumption ();
  void add_failing_assumption (const vector<int> &);
  void add_failing_assumption (int);
  void add_updated_clause (Clause *);

  void delete_clause (const vector<int> &, bool original = false);
  void delete_clause (Clause *);

  void deallocate_clause (Clause *);
  void update_moved_counterparts ();

  bool core (Clause *) const;
  void trim (ClauseIterator &);

  ColorRange& range(Clause *);
  void pick_new_color (int c = 0);
  void init_range (const Clause *);
  void join_range (int);
  void join_range (Clause *);
  void add_range (Clause *c);
  void assign_range (Clause *);
  void reset_range ();

  void trim_and_replay (ClauseIterator *, ResolutionIterator &);
  void trace_check (const char *);

  void print_stats ();
};

} // namespace CaDiCaL

#endif
