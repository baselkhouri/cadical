#ifndef _drup2itptypes_hpp_INCLUDED
#define _drup2itptypes_hpp_INCLUDED

#include <cassert>
#include <vector>

namespace CaDiCaLDRUP2Itp {

using namespace std;

struct Clause {
  Clause *next;
  uint64_t hash;
  uint64_t id;
  bool garbage;
  bool core;
  bool redundant;
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

struct Watch {
  Clause *clause;
  int blit;
  int size;
  Watch (int b, Clause *c) : clause (c), blit (b), size (c->size) {}
  Watch () {}
  bool binary () const { return size == 2; }
};

typedef vector<Watch> Watches;
typedef Watches::iterator watch_iterator;
typedef Watches::const_iterator const_watch_iterator;

inline void remove_watch (Watches &ws, Clause *clause) {
  const auto end = ws.end ();
  auto i = ws.begin ();
  for (auto j = i; j != end; j++) {
    const Watch &w = *i++ = *j;
    if (w.clause == clause)
      i--;
  }
  assert (i + 1 == end);
  ws.resize (i - ws.begin ());
}

inline void update_watch_size (Watches &ws, int blit, Clause *conflict) {
  bool found = false;
  const int size = conflict->size;
  for (Watch &w : ws) {
    if (w.clause == conflict)
      w.size = size, w.blit = blit, found = true;
    assert (w.clause->garbage || w.size == 2 || w.clause->size != 2);
  }
  assert (found), (void) found;
}

class WatchSort {
  vector<unsigned> trail;
  const signed char *vals;

public:
  WatchSort (const vector<unsigned> &lit2trail, const signed char *values)
      : trail (lit2trail), vals (values) {}
  bool operator() (int x, int y) const {
    assert (x && y);
    assert (abs (x) < trail.size ());
    assert (abs (y) < trail.size ());
    if (!vals[x])
      return true;
    if (!vals[y])
      return false;
    if (trail[abs (x)] > trail[abs (y)])
      return true;
    return false;
  }
};

} // namespace CaDiCaLDRUP2Itp

#endif
