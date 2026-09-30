#!/usr/bin/env python3
"""Extract the UNSAT core mechanism for two END_BIG defect-2 rows
(sinkset={P,Q}, n=3..6): which named constraints drive the kill."""
import sys
import itertools
from z3 import (Real, Bool, And, Or, Not, Solver, Int, If, sat, unsat)
from r3_profile_check import (ROWS, CHORDS, build,
                              transitivity_constraints,
                              row_score_constraints,
                              anchor_score_constraints)
from r3_sink_tests import end_gaps


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    theta, pi, phi, up, base = build(n)
    # find one orientation leaf where 2-sink is "least dead": we want a
    # leaf that is SAT without sink constraints but UNSAT with them.
    for bits in itertools.product([False, True], repeat=len(CHORDS)):
        up_val = dict(zip(CHORDS, bits))
        tcons = transitivity_constraints(up_val, theta, phi)
        if tcons is None:
            continue
        s0 = Solver()
        s0.add(*base, *tcons)
        for c, b in up_val.items():
            s0.add(up[c] == b)
        for r in ROWS:
            cons, _ = row_score_constraints(
                theta, pi, phi, r, n, ('>=', 3) if r == "h" else 2)
            s0.add(*cons)
        s0.add(*anchor_score_constraints(theta, pi, n))
        if s0.check() != sat:
            continue
        # leaf is alive; now add P,Q endbig
        g0p, g3p, _, _ = end_gaps(theta, pi, phi, "p")
        g0q, g3q, _, _ = end_gaps(theta, pi, phi, "q")
        s0.push()
        s0.add(g0p >= 1, g3p >= 1, g0q >= 1, g3q >= 1)
        if s0.check() == unsat:
            edges = sorted((x, y) if b else (y, x)
                           for (x, y), b in up_val.items())
            print("LEAF ORDER:", ' '.join(f'{a}->{b}' for a, b in edges))
            core = s0.unsat_core()
            # note: unsat_core needs tracked assertions; do a manual
            # minimize instead: try dropping each of the four big-gap
            # bounds
            for name, e in [("p_first>=1", g0p >= 1), ("p_last>=1", g3p >= 1),
                            ("q_first>=1", g0q >= 1), ("q_last>=1", g3q >= 1)]:
                s0.pop()
                s0.push()
                cons = [g0p >= 1, g3p >= 1, g0q >= 1, g3q >= 1]
                s0.add(*[c for c, (nm, _) in zip(cons,
                         [("p_first>=1", 0), ("p_last>=1", 0),
                          ("q_first>=1", 0), ("q_last>=1", 0)])
                        if nm != name])
                print(f"  drop {name}: {s0.check()}")
            s0.pop()
            # which row defect equations are essential? try relaxing
            # each low row's defect to 'free'
            return
        s0.pop()


if __name__ == "__main__":
    main()
