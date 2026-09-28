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


from z3 import Int, If


def row_score_constraints(theta, pi, phi, row, n, defect):
    """Positions of `row` = its three incident phi's, lifted by +pi iff
    p < theta_row.  Sorted -> four gaps over [theta, theta+pi) -> the
    defect equation  sum(max(floor(g)-1,0)) = n - defect.
    Returns (constraints, gap_list, lifted_flag_exprs)."""
    inc = [cd for cd in CHORDS if row in cd]
    th = theta[row]
    poss, lifts = [], {}
    for cd in inc:
        p = phi[cd]
        l = p < th
        poss.append(If(l, p + pi, p))
        lifts[cd] = l
    # sorted s0<=s1<=s2 via pairwise mins — encode with three sorted vars
    p0, p1, p2 = poss
    s0 = If(And(p0 <= p1, p0 <= p2), p0,
        If(p1 <= p2, p1, p2))
    s2 = If(And(p0 >= p1, p0 >= p2), p0,
        If(p1 >= p2, p1, p2))
    s1 = p0 + p1 + p2 - s0 - s2
    gaps = [s0 - th, s1 - s0, s2 - s1, th + pi - s2]
    cons = []
    score_terms = []
    for i, g in enumerate(gaps):
        k = Int(f"k_{row}{i}")
        cons += [k >= 0, k <= g, g < k + 1]
        score_terms.append(If(k - 1 > 0, k - 1, 0))
    cons.append(sum(score_terms) == n - defect)
    return cons, gaps, lifts


def anchor_score_constraints(theta, pi, n):
    """Anchor row: positions = the four thetas in [0, pi), defect 1."""
    ts = [theta[r] for r in ROWS]
    t0, t1, t2, t3 = ts
    s = list(ts)
    srt = []
    # simple insertion into a sorted list of 4 via ite — use sorting net
    a, b, c, d = ts
    x1 = If(a < b, a, b); y1 = If(a < b, b, a)
    x2 = If(c < d, c, d); y2 = If(c < d, d, c)
    lo1 = If(x1 < x2, x1, x2); hi2 = If(y1 < y2, y2, y1)
    midA = If(x1 < x2, x2, x1); midB = If(y1 < y2, y1, y2)
    m0 = If(midA < midB, midA, midB); m1 = If(midA < midB, midB, midA)
    ordered = [lo1, m0, m1, hi2]
    pts = [0] + ordered + [pi]
    gaps = [pts[i + 1] - pts[i] for i in range(5)]
    cons = []
    terms = []
    for i, g in enumerate(gaps):
        k = Int(f"k_anc{i}")
        cons += [k >= 0, k <= g, g < k + 1]
        terms.append(If(k - 1 > 0, k - 1, 0))
    cons.append(sum(terms) == n - 1)
    return cons


def h_merge_constraint(theta, pi, phi, defect):
    """Row h defect = 2 + mu where mu = floor(g2+g3)-floor(g2)-floor(g3)+1.
    defect=3 -> floor(g2+g3) = floor(g2)+floor(g3)  (no extra carry).
    Here g2 = p_ht - p_hb, g3 = theta_h + pi - p_ht."""
    g2 = phi[("h", "t")] - phi[("h", "b")]
    g3 = theta["h"] + pi - phi[("h", "t")]
    k2, k3, k23 = Int("kg2"), Int("kg3"), Int("kg23")
    cons = [k2 >= 0, k2 <= g2, g2 < k2 + 1,
            k3 >= 0, k3 <= g3, g3 < k3 + 1,
            k23 >= 0, k23 <= g2 + g3, g2 + g3 < k23 + 1,
            k23 == k2 + k3 + defect - 3]
    return cons


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
    alive = []
    for idx, (up_val, s, tcons, paths) in enumerate(leaves, 1):
        # ---- Score/defect layer: defect 2 on a,b,t; defect 3 on h;
        # anchor defect 1.  A leaf UNSAT here is already dead by
        # pure score arithmetic (no extra geometry needed in Lean).
        s2 = Solver()
        s2.add(*base, *tcons)
        for c, b in up_val.items():
            s2.add(up[c] == b)
        gaps_by_row = {}
        for r in ROWS:
            cons, gaps, _ = row_score_constraints(
                theta, pi, phi, r, n, 3 if r == "h" else 2)
            s2.add(*cons)
            gaps_by_row[r] = gaps
        s2.add(*anchor_score_constraints(theta, pi, n))
        s2.add(*h_merge_constraint(theta, pi, phi, 3))
        verdict = s2.check()
        print(f"=== LEAF {idx} ===   score-layer: {verdict}")
        if verdict == unsat:
            print("(DEAD: direction geometry + defect equations inconsistent)")
            print()
            continue
        alive.append(idx)
        s = s2   # report facts under the full (geometry + score) model
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
        print("ROW_h: theta_h < phi_ha < phi_hb < phi_ht   (fixed)")
        # Full forced order of each row's three chord positions, with the
        # lift decision (position < theta_x means it lands at the top of
        # the row's [theta_x, theta_x+pi) interval).
        for x in ("a", "b", "t"):
            inc = [c for c in CHORDS if x in c]
            items = []
            for cd in inc:
                p = phi[cd]
                nm = phi_name(*cd)
                vs_theta = forced_facts(s, p < theta[x])
                items.append((p, nm, vs_theta))
            lifted = [it for it in items if it[2] == "FORCED"]      # p<θ: sits at top via +π
            raw = [it for it in items if it[2] == "FORCED_NOT"]   # p≥θ: stays low
            ambig_lift = [it for it in items if it[2] == "FREE"]

            def sort_forced(its):
                seq = list(its)
                for i in range(len(seq)):
                    for j in range(i + 1, len(seq)):
                        if forced_facts(s, seq[j][0] < seq[i][0]) == "FORCED":
                            seq[i], seq[j] = seq[j], seq[i]
                ambig = []
                for i in range(len(seq)):
                    for j in range(i + 1, len(seq)):
                        if forced_facts(s, seq[i][0] < seq[j][0]) != "FORCED":
                            ambig.append((seq[i][1], seq[j][1]))
                return " < ".join(it[1] for it in seq), ambig

            raw_s, raw_amb = sort_forced(raw)
            lift_s, lift_amb = sort_forced(lifted)
            row_str = f"theta_x < {raw_s}" if raw_s else "theta_x"
            if lift_s:
                row_str += f"  | TOP(+pi): {lift_s}"
            extra = ""
            if ambig_lift:
                extra += f"  LIFT-FREE: {[it[1] for it in ambig_lift]}"
            if raw_amb or lift_amb:
                extra += f"  ORD-AMBIG: {raw_amb + lift_amb}"
            print(f"ROW_{x}: {row_str}{extra}")
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
