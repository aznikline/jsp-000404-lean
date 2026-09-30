#!/usr/bin/env python3
"""r3_sink_tests.py — which sink patterns among low rows are abstractly
feasible in the R3 profile?

Row X's END_BIG predicate: first gap >= 1 AND last gap >= 1 (lam=1).
Test feasibility of the defect profile (2,2,2,>=3 / anchor 1) under
each subset S of {p,q,r} declared END_BIG.

usage: python3 tools/r3_sink_tests.py [n]
"""
import sys
import itertools
from z3 import (Real, Bool, And, Or, Not, Solver, Int, If, sat, unsat)
from r3_profile_check import (ROWS, CHORDS, build,
                              transitivity_constraints,
                              row_score_constraints,
                              anchor_score_constraints)


def end_gaps(theta, pi, phi, row):
    """Return (first_gap_expr, last_gap_expr) for `row` using the lifted
    sorted positions s0<=s1<=s2 in [theta, theta+pi)."""
    inc = [cd for cd in CHORDS if row in cd]
    th = theta[row]
    poss = [If(phi[cd] < th, phi[cd] + pi, phi[cd]) for cd in inc]
    p0, p1, p2 = poss
    s0 = If(And(p0 <= p1, p0 <= p2), p0, If(p1 <= p2, p1, p2))
    s2 = If(And(p0 >= p1, p0 >= p2), p0, If(p1 >= p2, p1, p2))
    return s0 - th, th + pi - s2, s0, s2


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    theta, pi, phi, up, base = build(n)
    results = {}
    for sinkset_bits in itertools.product([0, 1], repeat=3):
        sinkset = {r for r, b in zip(["p", "q", "r"], sinkset_bits) if b}
        tag = ''.join(r.upper() for r in sorted(sinkset)) or 'NONE'
        n_sat = 0
        models = []
        for bits in itertools.product([False, True], repeat=len(CHORDS)):
            up_val = dict(zip(CHORDS, bits))
            tcons = transitivity_constraints(up_val, theta, phi)
            if tcons is None:
                continue
            s = Solver()
            s.add(*base, *tcons)
            for c, b in up_val.items():
                s.add(up[c] == b)
            for r in ROWS:
                cons, _ = row_score_constraints(
                    theta, pi, phi, r, n, ('>=', 3) if r == "h" else 2)
                s.add(*cons)
            s.add(*anchor_score_constraints(theta, pi, n))
            for r in sinkset:
                g0, g3, _, _ = end_gaps(theta, pi, phi, r)
                s.add(g0 >= 1, g3 >= 1)
            if s.check() == sat:
                n_sat += 1
                if len(models) < 2:
                    models.append(up_val)
        results[tag] = n_sat
        print(f"sinkset={tag:6s}  SAT leaves={n_sat}", flush=True)
        for uv in models:
            edges = sorted((x, y) if b else (y, x)
                           for (x, y), b in uv.items())
            print("   e.g. ORDER:", ' '.join(f'{a}->{b}' for a, b in edges))
    print("\nSUMMARY:", results)


if __name__ == "__main__":
    main()
