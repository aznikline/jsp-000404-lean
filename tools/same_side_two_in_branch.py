#!/usr/bin/env python3
"""same_side_two_in_branch.py — discovery enumerator for the F/F and L/L
same-side two-in leaves in the five-point R=3 SatChart model.

Model (lambda = 1 unit, n = 3 primary; n parametric):

  Rows: h (defect 3), a b t (defect 2).  F/F means ShortWitness a->h and
  b->h both land in h's F window  [th+1, beta+1)  with beta = pi - n in
  (0,1).  Sender short-last is impossible there (needs phi > pi-1), so
  Up(h,a) and Up(h,b) are forced.  Free orientations: the four chords
  {h,t},{a,b},{a,t},{b,t}.  two_in_F_above fixes the h-row order
  phi_ha < phi_hb < phi_ht with defect(h) = 2 + mu.

  Per chord {x,y} exactly one of Up(x,y) / Up(y,x) holds; each choice
  gives the corridor bound  theta_src + 1 <= phi <= pi - 1 + theta_dst.
  For each Up path x->y->z:  Up(x,z) must hold (transitivity) and
  phi_xz lies strictly between phi_xy and phi_yz (betweenness), plus
  the cap |phi_yz - phi_xy| >= 1.

Usage: python3 tools/same_side_two_in_branch.py [n]
Output: one leaf block per surviving orientation pattern with the fields
the takeover doc asks for (ORDER / ROW orders / CAPS / consumers /
candidate contradiction hooks).
"""

import sys
import itertools
from z3 import (Real, Bool, And, Or, Not, Solver, sat, unsat)

ROWS = ["h", "a", "b", "t"]
# undirected chords -> canonical (x, y) with variable phi_xy
CHORDS = [("h", "a"), ("h", "b"), ("h", "t"), ("a", "b"), ("a", "t"), ("b", "t")]


def phi_name(x, y):
    return f"p_{x}{y}"


def build(n=3):
    """Return (vars, base_constraints, chord_bools)."""
    th, ta, tb, tt = (Real(f"th"), Real("ta"), Real("tb"), Real("tt"))
    pi = Real("pi")
    theta = {"h": th, "a": ta, "b": tb, "t": tt}
    phi = {c: Real(phi_name(*c)) for c in CHORDS}

    # Up(x,y) chosen?  For each chord a Bool; True means Up(x,y).
    up = {c: Bool(f"up_{c[0]}{c[1]}") for c in CHORDS}

    base = [
        pi > n, pi < n + 1,                      # beta = pi - n in (0,1)
        th >= 0, th <= pi - n,
        ta >= 0, ta <= pi - n,
        tb >= 0, tb <= pi - n,
        tt >= 0, tt <= pi - n,
        theta["h"] < ta,                          # F/F: both senders above h
        theta["h"] < tb,
    ]
    # chord ranges + corridor bounds driven by the orientation bool
    for (x, y) in CHORDS:
        p = phi[(x, y)]
        base += [p >= 0, p < pi]
        base.append(
            Or(
                And(up[(x, y)], theta[x] + 1 <= p, p <= pi - 1 + theta[y]),
                And(Not(up[(x, y)]), theta[y] + 1 <= p, p <= pi - 1 + theta[x]),
            )
        )
    # h-row F windows and order: xa < xb < z all >= th+1, F-window < pi-n+1
    base += [
        theta["h"] + 1 <= phi[("h", "a")],
        phi[("h", "a")] < phi[("h", "b")],
        phi[("h", "b")] < phi[("h", "t")],
        phi[("h", "b")] < pi - n + 1,
    ]
    # senders short-first (raw): phi_sh - theta_s < 1
    base += [phi[("h", "a")] - ta < 1, phi[("h", "b")] - tb < 1]
    # forced orientations
    forced = {("h", "a"): True, ("h", "b"): True}
    return theta, pi, phi, up, base, forced


def up_dir(up_val, x, y):
    """Chosen direction of chord {x,y} as (src,dst)."""
    return (x, y) if up_val else (y, x)


def transitivity_constraints(up_val, theta, phi):
    """For every path x->y->z: need Up(x,z) and strict betweenness."""
    cons = []
    edges = {(x, y): up_dir(v, x, y) for (x, y), v in up_val.items()}
    chosen = set()
    for (x, y), v in up_val.items():
        chosen.add(up_dir(v, x, y))
    # build adjacency
    nbr = {}
    for s_, d_ in chosen:
        nbr.setdefault(s_, []).append(d_)
    paths = []
    for x in ROWS:
        for y in nbr.get(x, []):
            for z in nbr.get(y, []):
                if z == x:
                    return None, []          # 2-cycle impossible anyway
                paths.append((x, y, z))
    for (x, y, z) in paths:
        if (x, z) not in chosen:
            return None, []                  # transitivity demands Up(x,z)
        def pv(i, j):
            key = (i, j) if (i, j) in phi else (j, i)
            return phi[key]
        pxy, pyz, pxz = pv(x, y), pv(y, z), pv(x, z)
        cons += [pxz > pxy, pxz > pyz] if False else []
        cons.append(Or(And(pxy < pxz, pxz < pyz),
                       And(pyz < pxz, pxz < pxy)))
        # cap: lam <= |pyz - pxy|
        cons.append(Or(pxy + 1 <= pyz, pyz + 1 <= pxy))
    return cons, paths


def forced_facts(solver, expr):
    solver.push()
    solver.add(expr)
    r1 = solver.check()
    solver.pop()
    solver.push()
    solver.add(Not(expr))
    r2 = solver.check()
    solver.pop()
    if r1 == sat and r2 == unsat:
        return "FORCED"
    if r1 == unsat and r2 == sat:
        return "FORCED_NOT"
    return "FREE"


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    theta, pi, phi, up, base, forced = build(n)
    free_chords = [c for c in CHORDS if c not in forced]

    leaves = []
    for bits in itertools.product([False, True], repeat=len(free_chords)):
        up_val = dict(forced)
        for c, b in zip(free_chords, bits):
            up_val[c] = b
        tcons, paths = transitivity_constraints(up_val, theta, phi)
        if tcons is None:
            continue
        s = Solver()
        s.add(*base, *tcons)
        for c, b in up_val.items():
            s.add(up[c] == b)
        if s.check() != sat:
            continue
        leaves.append((up_val, s, tcons, paths))

    print(f"n={n}  F/F enumeration: {len(leaves)} feasible order leaves\n")
    for idx, (up_val, s, tcons, paths) in enumerate(leaves, 1):
        # For each sender row and t row, determine lifted-order facts that
        # are forced: phi_hx vs theta_x etc.
        def classify(x):
            r = forced_facts(s, phi[("h", x)] < theta[x])
            return {"FORCED": "phi<th (h-chord LIFTED to top of row)",
                    "FORCED_NOT": "phi>th (h-chord stays low)",
                    "FREE": "both lift cases open"}[r]
        lifts = {x: classify(x) for x in ("a", "b", "t")}
        # theta order facts
        t_pos = []
        for (x, y, nm) in [("t", "h", "tt<th"), ("h", "t", "th<tt"),
                           ("t", "a", "tt<ta"), ("t", "b", "tt<tb"),
                           ("a", "t", "ta<tt"), ("b", "t", "tb<tt")]:
            f = forced_facts(s, theta[x] < theta[y])
            if f == "FORCED":
                t_pos.append(nm)
        edges = sorted(up_dir(v, x, y) for (x, y), v in up_val.items())
        print(f"=== LEAF {idx} ===")
        print("ORDER (Up edges):", " ".join(f"{x}->{y}" for x, y in edges))
        # Resolve each up_trans betweenness disjunction to its forced side.
        def pv(i, j):
            key = (i, j) if (i, j) in phi else (j, i)
            return phi[key], phi_name(*key)
        for (x, y, z) in paths:
            pxy, nxy = pv(x, y)
            pyz, nyz = pv(y, z)
            pxz, nxz = pv(x, z)
            lo = forced_facts(s, And(pxy < pxz, pxz < pyz))
            hi = forced_facts(s, And(pyz < pxz, pxz < pxy))
            if lo == "FORCED":
                r = f"{nxy} < {nxz} < {nyz}"
            elif hi == "FORCED":
                r = f"{nyz} < {nxz} < {nxy}"
            else:
                r = f"BOTH_DISJUNCTS_OPEN ({nxy}<{nxz}<{nyz} | {nyz}<{nxz}<{nxy})"
            print(f"PATH {x}->{y}->{z}: {r}   (cap |{nyz}-{nxy}| >= 1)")
        print("ROW_h: phi_ha < phi_hb < phi_ht   (fixed)")
        for x in ("a", "b", "t"):
            print(f"ROW_{x}: lift[h-chord?] {lifts[x]}")
        print("THETA:", ", ".join(t_pos) or "unconstrained")
        print("CAPS: see paths above (each path gives lam-separation)")
        print("NO_ADJACENT_CONSUMERS: defect-2 rows {a,b,t} — check row"
              " orders above for two adjacent big-gap candidates")
        print("SCORE_CONCENTRATION: check if some row's score collapses"
              " onto one gap")
        print("FINAL_CONTRADICTION: (to be filled during Lean phase)")
        print()


if __name__ == "__main__":
    main()
