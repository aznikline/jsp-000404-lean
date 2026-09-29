#!/usr/bin/env python3
"""same_side_two_in_ll.py — L/L mirror of same_side_two_in_branch.py.

L/L means ShortWitness a->h and b->h both land in h's L window
(pi-1 < phi <= pi-1+th).  Senders are forced short-last, hence
Up(a,h) and Up(b,h) (senders above h in the Up order).
two_in_L_below gives z = phi_ht < phi_ha < phi_hb with defect(h)=2+mu.

Usage: python3 tools/same_side_two_in_ll.py [n]
"""

import sys
import itertools
from z3 import (Real, Bool, And, Or, Not, Solver, sat, unsat)

sys.path.insert(0, "tools")
from same_side_two_in_branch import (
    ROWS, CHORDS, phi_name, up_dir, transitivity_constraints, forced_facts,
    row_score_constraints, anchor_score_constraints,
)
from z3 import Int, If


def build_ll(n=3):
    th, ta, tb, tt = (Real("th"), Real("ta"), Real("tb"), Real("tt"))
    pi = Real("pi")
    theta = {"h": th, "a": ta, "b": tb, "t": tt}
    phi = {c: Real(phi_name(*c)) for c in CHORDS}
    up = {c: Bool(f"up_{c[0]}{c[1]}") for c in CHORDS}

    base = [
        pi > n, pi < n + 1,
        th >= 0, th <= pi - n,
        ta >= 0, ta <= pi - n,
        tb >= 0, tb <= pi - n,
        tt >= 0, tt <= pi - n,
        ta < th,                              # L/L: senders below h
        tb < th,
    ]
    for (x, y) in CHORDS:
        p = phi[(x, y)]
        base += [p >= 0, p < pi]
        base.append(
            Or(
                And(up[(x, y)], theta[x] + 1 <= p, p <= pi - 1 + theta[y]),
                And(Not(up[(x, y)]), theta[y] + 1 <= p, p <= pi - 1 + theta[x]),
            )
        )
    # Row h: z < u < w, received directions in L window (pi-1, pi-1+th].
    base += [
        phi[("h", "t")] < phi[("h", "a")],
        phi[("h", "a")] < phi[("h", "b")],
        pi - 1 < phi[("h", "a")],
        phi[("h", "b")] <= pi - 1 + th,
    ]
    # senders short-last: theta_s + pi - phi_sh < 1  (phi_sh = phi_hs)
    base += [theta["a"] + pi - phi[("h", "a")] < 1,
             theta["b"] + pi - phi[("h", "b")] < 1]
    forced = {("h", "a"): False, ("h", "b"): False}   # Up(a,h), Up(b,h)
    return theta, pi, phi, up, base, forced


def h_merge_constraint_ll(theta, pi, phi, defect):
    """L side: row-h sorted positions z < u < w (raw; z >= th forced?).
    gaps g0 = p_ht - th, g1 = p_ha - p_ht; defect = 2+mu, mu = carry."""
    g0 = phi[("h", "t")] - theta["h"]
    g1 = phi[("h", "a")] - phi[("h", "t")]
    k0, k1, k01 = Int("kg0"), Int("kg1"), Int("kg01")
    cons = [k0 >= 0, k0 <= g0, g0 < k0 + 1,
            k1 >= 0, k1 <= g1, g1 < k1 + 1,
            k01 >= 0, k01 <= g0 + g1, g0 + g1 < k01 + 1,
            k01 == k0 + k1 + defect - 3]
    return cons


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    theta, pi, phi, up, base, forced = build_ll(n)
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

    print(f"n={n}  L/L enumeration: {len(leaves)} feasible order leaves\n")
    alive = []
    for idx, (up_val, s, tcons, paths) in enumerate(leaves, 1):
        s2 = Solver()
        s2.add(*base, *tcons)
        for c, b in up_val.items():
            s2.add(up[c] == b)
        for r in ROWS:
            cons, gaps, _ = row_score_constraints(
                theta, pi, phi, r, n, 3 if r == "h" else 2)
            s2.add(*cons)
        s2.add(*anchor_score_constraints(theta, pi, n))
        s2.add(*h_merge_constraint_ll(theta, pi, phi, 3))
        verdict = s2.check()
        edges = sorted(up_dir(v, x, y) for (x, y), v in up_val.items())
        print(f"=== LEAF {idx} ===   score-layer: {verdict}")
        print("ORDER (Up edges):", " ".join(f"{x}->{y}" for x, y in edges))
        if verdict == unsat:
            print("(DEAD: direction geometry + defect equations inconsistent)")
            print()
            continue
        alive.append(idx)
        s = s2
        t_pos = []
        for (x, y, nm) in [("t", "h", "tt<th"), ("h", "t", "th<tt"),
                           ("t", "a", "tt<ta"), ("t", "b", "tt<tb"),
                           ("a", "t", "ta<tt"), ("b", "t", "tb<tt"),
                           ("a", "h", "ta<th"), ("b", "h", "tb<th"),
                           ("a", "b", "ta<tb"), ("b", "a", "tb<ta")]:
            f = forced_facts(s, theta[x] < theta[y])
            if f == "FORCED":
                t_pos.append(nm)
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
                r = f"BOTH ({nxy}<{nxz}<{nyz} | {nyz}<{nxz}<{nxy})"
            print(f"PATH {x}->{y}->{z}: {r}   (cap |{nyz}-{nxy}| >= 1)")
        print("ROW_h: p_ht < p_ha < p_hb <= pi-1+th   (z<th lift open?)")
        for x in ("a", "b", "t", "h"):
            inc = [c for c in CHORDS if x in c]
            items = []
            for cd in inc:
                p = phi[cd]
                nm = phi_name(*cd)
                vs_theta = forced_facts(s, p < theta[x])
                items.append((p, nm, vs_theta))
            lifted = [it for it in items if it[2] == "FORCED"]
            raw = [it for it in items if it[2] == "FORCED_NOT"]
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
        print()


if __name__ == "__main__":
    main()
