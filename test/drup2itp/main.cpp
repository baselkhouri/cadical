#include "../../contrib/drup2itp.hpp"
#include "../../src/cadical.hpp"
#include "../../src/solver.cpp"
#include <iostream>
#include <vector>

#ifdef NDEBUG
#undef NDEBUG
#endif

extern "C" {
#include <assert.h>
}

using namespace std;
using namespace CaDiCaL;

static void formula (CaDiCaL::Solver &solver) {
  for (int r = -1; r < 2; r += 2)
    for (int s = -1; s < 2; s += 2)
      for (int t = -1; t < 2; t += 2)
        solver.add (r * 1), solver.add (s * 2), solver.add (t * 3),
            solver.add (0);
}

int main () {
  Solver solver, verifier;
  ClauseCopier copier (verifier);
  CaDiCaLDRUP2Itp::Drup2Itp drupper;
  solver.connect_proof_tracer (&drupper, true);
  formula (solver);
  int res = solver.solve ();
  assert (res == 20);
  drupper.trim (copier);
  res = verifier.solve ();
  assert (res == 20);
  solver.disconnect_proof_tracer (&drupper);
  return 0;
}
