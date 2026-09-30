#!/usr/bin/env python3
"""r3_profile_check.py — is the bare R3 defect profile already UNSAT in
the direction/floor model?

Model: SatChart Fin 4 non-anchor rows {p,q,r,h} (defects 2,2,2,>=3),
anchor defect 1.  No witness-edge assumptions -- only Up-orientation
geometry (corridor + transitivity + betweenness + cap) and the row
defect equations.

If some orientation leaf is SAT, the pure profile is NOT abstractly
impossible: the R3 closure must use end-gap / ShortWitness structure.
If all leaves are UNSAT, R3 dies at score/arithmetic level.

usage: python3 tools/r3_profile_check.py [n]
"""
import sys
import itertools
from z3 import Real, Bool, And, Or, Not, Solver, Int, If, sat, unsat

ROWS = ["p", "q", "r", "h"]
CHORDS = list(itertools.combinations(ROWS, 2))


def phi_name(x, y):
    return f"p_{x}{y}"


def transitivity_constraints(up_val, theta, phi):
    cons = []
    chosen = {(x, y) if v else (y, x) for (x, y), v in up_val.items()}
    nbr = {}
    for s_, d_ in chosen:
        nbr.setdefault(s_, []).append(d_)
    for x in ROWS:
        for y in nbr.get(x, []):
            for z in nbr.get(y, []):
                if z == x:
                    return None
                if (x, z) not in chosen:
                    return None
                def pv(i, j):
                    k = (i, j) if (i, j) in phi else (j, i)
                    return phi[k]
                pxy, pyz, pxz = pv(x, y), pv(y, z), pv(x, z)
                cons.append(Or(And(pxy < pxz, pxz < pyz),
                               And(pyz < pxz, pxz < pxy)))
                cons.append(Or(pxy + 1 <= pyz, pyz + 1 <= pxy))
    return cons


def row_score_constraints(theta, pi, phi, row, n, defect_expr):
    """defect_expr: int (exact) or ('>=',k).  Returns (cons, gaps)."""
    inc = [cd for cd in CHORDS if row in cd]
    th = theta[row]
    poss = [If(phi[cd] < th, phi[cd] + pi, phi[cd]) for cd in inc]
    p0, p1, p2 = poss
    s0 = If(And(p0 <= p1, p0 <= p2), p0, If(p1 <= p2, p1, p2))
    s2 = If(And(p0 >= p1, p0 >= p2), p0, If(p1 >= p2, p1, p2))
    s1 = p0 + p1 + p2 - s0 - s2
    gaps = [s0 - th, s1 - s0, s2 - s1, th + pi - s2]
    cons, terms = [], []
    for i, g in enumerate(gaps):
        k = Int(f"k_{row}{i}")
        cons += [k >= 0, k <= g, g < k + 1]
        terms.append(If(k - 1 > 0, k - 1, 0))
    total = sum(terms)
    if isinstance(defect_expr, tuple):
        cons.append(total <= n - defect_expr[1])   # defect >= k
    else:
        cons.append(total == n - defect_expr)
    return cons, gaps


def anchor_score_constraints(theta, pi, n):
    ts = [theta[r] for r in ROWS]
    a, b, c, d = ts
    x1 = If(a < b, a, b); y1 = If(a < b, b, a)
    x2 = If(c < d, c, d); y2 = If(c < d, d, c)
    lo1 = If(x1 < x2, x1, x2); hi2 = If(y1 < y2, y2, y1)
    midA = If(x1 < x2, x2, x1); midB = If(y1 < y2, y1, y2)
    m0 = If(midA < midB, midA, midB); m1 = If(midA < midB, midB, midA)
    ordered = [lo1, m0, m1, hi2]
    pts = [0] + ordered + [pi]
    gaps = [pts[i + 1] - pts[i] for i in range(5)]
    cons, terms = [], []
    for i, g in enumerate(gaps):
        k = Int(f"k_anc{i}")
        cons += [k >= 0, k <= g, g < k + 1]
        terms.append(If(k - 1 > 0, k - 1, 0))
    cons.append(sum(terms) == n - 1)
    return cons


def build(n=3):
    theta = {r: Real(f"th_{r}") for r in ROWS}
    pi = Real("pi")
    phi = {c: Real(phi_name(*c)) for c in CHORDS}
    up = {c: Bool(f"up_{c[0]}{c[1]}") for c in CHORDS}
    base = [pi > n, pi < n + 1]
    base += [theta[r] >= 0 for r in ROWS]
    base += [theta[r] <= pi - n for r in ROWS]
    for (x, y) in CHORDS:
        p = phi[(x, y)]
        base += [p >= 0, p < pi]
        base.append(Or(
            And(up[(x, y)], theta[x] + 1 <= p, p <= pi - 1 + theta[y]),
            And(Not(up[(x, y)]), theta[y] + 1 <= p, p <= pi - 1 + theta[x])))
    return theta, pi, phi, up, base


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    theta, pi, phi, up, base = build(n)
    sat_leaves, unsat_leaves, dead_orient = [], [], 0
    for bits in itertools.product([False, True], repeat=len(CHORDS)):
        up_val = dict(zip(CHORDS, bits))
        tcons = transitivity_constraints(up_val, theta, phi)
        if tcons is None:
            dead_orient += 1
            continue
        s = Solver()
        s.add(*base, *tcons)
        for c, b in up_val.items():
            s.add(up[c] == b)
        for r in ROWS:
            cons, _ = row_score_constraints(
                theta, pi, phi, r, n,
                ('>=', 3) if r == "h" else 2)
            s.add(*cons)
        s.add(*anchor_score_constraints(theta, pi, n))
        v = s.check()
        if v == sat:
            sat_leaves.append((up_val, s))
        else:
            unsat_leaves.append(up_val)
    print(f"n={n} R3 pure-profile: dead-orientations={dead_orient} "
          f"UNSAT leaves={len(unsat_leaves)} SAT leaves={len(sat_leaves)}")
    for i, (uv, s) in enumerate(sat_leaves[:20]):
        edges = sorted((x, y) if b else (y, x) for (x, y), b in uv.items())
        print(f"SAT leaf {i}: {' '.join(f'{a}->{b}' for a, b in edges)}")


if __name__ == "__main__":
    main()
