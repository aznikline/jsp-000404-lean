#!/usr/bin/env python3
"""r3_class_synth.py — exact branch synthesis over the canonical DAG
classes produced by tools/r3_witness_dag.py.

For each canonical class (labeled functional digraph + type assignment)
build the abstract z3 leaf:

    base model  (Up orientations, corridor, transitivity, cap)
    + row defect equations   (defect(p)=defect(q)=defect(r)=2,
                              defect(h)>=3, anchor defect=1)
    + per-class structural constraints:
        X -F-> Y  :  first gap of X < lam  AND  head chord = phi_XY
                     (lift_X(phi_XY) is row X's min lifted position
                      and lies < theta_X + 1)
        X -L-> Y  :  last gap of X < lam  AND  getLast chord = phi_XY
        X sink    :  first gap >= 1 AND last gap >= 1
        X Type I  :  exactly one gap >= 1   (rowBig = 1)
        X Type II :  exactly two gaps >= 1  (rowBig = 2)
      (existence of the listed edges + sink conditions only; other
       chords unconstrained -- monotone-inclusion principle: any
       extra real edges only add witnesses, they cannot rescue a class)

An orientation leaf = choice of Up direction on all 6 chords that is
consistent with transitivity.  A class is ABSTRACT-UNSAT iff every
orientation leaf is UNSAT under its structural constraints.  SAT leaves
are preserved verbatim.

usage: python3 tools/r3_class_synth.py [n] [class_ids...]
"""
import sys
import itertools
import json
from z3 import (Real, Bool, And, Or, Not, Solver, Int, If, sat, unsat)
from r3_profile_check import (ROWS, CHORDS, build,
                              transitivity_constraints,
                              row_score_constraints,
                              anchor_score_constraints)

VERTEX = {'p': 'P', 'q': 'Q', 'r': 'R', 'h': 'H'}
RVERTEX = {v: k for k, v in VERTEX.items()}


def true_dir(phi, up, pi, a, b):
    """True direction of vector a->b: phi if Up(a,b), else phi - pi."""
    if (a, b) in phi:
        return If(up[(a, b)], phi[(a, b)], phi[(a, b)] - pi)
    return If(up[(b, a)], phi[(b, a)] - pi, phi[(b, a)])


def fold_pi(diff, pi):
    adiff = If(diff >= 0, diff, -diff)
    return If(adiff <= pi, adiff, 2 * pi - adiff)


def triangle_angle_sums(phi, up, pi):
    """Interior-angle sum = pi for every triple of non-anchor rows.

    Purely piecewise-linear given the Up bits: the interior angle at v
    between rays v->u and v->w is |d_vw - d_vu| folded into (0, pi).
    """
    cons = []
    for x, y, z in itertools.combinations(ROWS, 3):
        total = 0
        for v, u, w in ((x, y, z), (y, x, z), (z, x, y)):
            total += fold_pi(
                true_dir(phi, up, pi, v, w) - true_dir(phi, up, pi, v, u), pi)
        cons.append(total == pi)
    return cons


def anchor_angle_sums(theta, phi, up, pi):
    """Interior-angle sum = pi for every anchor triangle (A,i,j).

    True direction of vector A->i is theta_i or theta_i - pi (free bit
    per vertex); vector i->A is its negative.  Piecewise linear.
    Returns (constraints, anchor-sign bools).
    """
    # htheta: oangle e (c_i - c_v) = theta_i, theta_i in [0, pi-n*lam]
    #  => true dir of A->i is exactly theta_i; i->A is theta_i - pi.
    def da(i):
        return theta[i]

    def diA(i):
        return theta[i] - pi

    cons = []
    for i, j in itertools.combinations(ROWS, 2):
        total = fold_pi(da(j) - da(i), pi)
        # angle at i between rays i->A and i->j
        total += fold_pi(true_dir(phi, up, pi, i, j) - diA(i), pi)
        total += fold_pi(true_dir(phi, up, pi, j, i) - diA(j), pi)
        cons.append(total == pi)
    return cons


def lifted_positions(theta, pi, phi, row):
    inc = [cd for cd in CHORDS if row in cd]
    th = theta[row]
    return {cd: If(phi[cd] < th, phi[cd] + pi, phi[cd]) for cd in inc}


def row_structure(theta, pi, phi, row):
    """Sorted lifted positions s0<=s1<=s2 and the four gaps."""
    lp = lifted_positions(theta, pi, phi, row)
    vals = list(lp.items())
    (c0, p0), (c1, p1), (c2, p2) = vals
    s0 = If(And(p0 <= p1, p0 <= p2), p0, If(p1 <= p2, p1, p2))
    s2 = If(And(p0 >= p1, p0 >= p2), p0, If(p1 >= p2, p1, p2))
    s1 = p0 + p1 + p2 - s0 - s2
    gaps = [s0 - theta[row], s1 - s0, s2 - s1, theta[row] + pi - s2]
    return lp, s0, s2, gaps


def class_constraints(cls, theta, pi, phi, n):
    """z3 constraints for one canonical class."""
    cons = []
    edges = {}   # (src,dst) -> label, vertex names P,Q,R,H -> lowercase
    for e in cls['edges']:
        # 'P-[F]->Q'
        a, rest = e.split('-[')
        l, b = rest[0], rest.split(']->')[1]
        edges[(RVERTEX[a], RVERTEX[b])] = l
    outmap = {v: {'F': None, 'L': None} for v in ROWS}
    inmap = {v: [] for v in ROWS}
    for (a, b), l in edges.items():
        outmap[a][l] = b
        inmap[b].append((a, l))
    sinks = [RVERTEX[v] for v in cls['sinks']]
    types = {RVERTEX[k]: v for k, v in cls['types'].items()}
    sigs = {RVERTEX[k]: v for k, v in
            cls.get('sink_signatures', {}).items()}

    for x in ROWS:
        lp, s0, s2, gaps = row_structure(theta, pi, phi, x)
        if x in ['p', 'q', 'r']:
            ty = types[x]
            bigs = [If(g >= 1, 1, 0) for g in gaps]
            cons.append(sum(bigs) == (1 if ty == 'I' else 2))
        if x in sinks:
            cons += [gaps[0] >= 1, gaps[3] >= 1]
            sg = sigs.get(x)
            if sg == 'SIG_A':   # received F: g0 in [1,2), g3 >= n-1
                cons += [gaps[0] < 2, gaps[3] >= n - 1]
            elif sg == 'SIG_B':  # received L: g3 in [1,2), g0 >= n-1
                cons += [gaps[3] < 2, gaps[0] >= n - 1]
        for l in ('F', 'L'):
            t = outmap[x][l]
            if t is None:
                # canonical witness absent => that end gap is big
                # (short first gap always yields the head witness)
                if x in ['p', 'q', 'r', 'h']:
                    cons.append(
                        gaps[0] >= 1 if l == 'F' else gaps[3] >= 1)
                continue
            cd = (x, t) if (x, t) in lp else (t, x)
            p = lp[cd]
            if l == 'F':
                # p is row-x min position and first gap short
                cons += [p == s0, p - theta[x] < 1]
            else:
                cons += [p == s2, theta[x] + pi - p < 1]
        # receiver-emitter positional facts (defect-2 rows only):
        #   defect_two_last_recv_head_lt   : recv L-edge from y,
        #     own first gap short  =>  head < phi_{x,y}
        #   defect_two_first_recv_getLast_gt : recv F-edge from y,
        #     own last gap short   =>  phi_{x,y} < getLast
        if x in ['p', 'q', 'r']:
            for a, l in inmap[x]:
                cd = (x, a) if (x, a) in lp else (a, x)
                if l == 'L' and outmap[x]['F'] is not None:
                    cons.append(s0 < lp[cd])
                if l == 'F' and outmap[x]['L'] is not None:
                    cons.append(lp[cd] < s2)
    return cons, edges


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    only = set(sys.argv[2:])
    theta, pi, phi, up, base = build(n)
    classes = json.load(open('R3_DAG_CLASSES.json'))
    results = {'UNSAT': [], 'SAT': [], 'unknown': []}
    sat_dump = []
    for cls in classes:
        cid = cls['id']
        if only and cid not in only:
            continue
        ccons, edges = class_constraints(cls, theta, pi, phi, n)
        n_unsat, sat_leaves = 0, []
        for bits in itertools.product([False, True], repeat=len(CHORDS)):
            up_val = dict(zip(CHORDS, bits))
            tcons = transitivity_constraints(up_val, theta, phi)
            if tcons is None:
                continue
            s = Solver()
            s.add(*base, *tcons, *ccons)
            s.add(*triangle_angle_sums(phi, up, pi))
            s.add(*anchor_angle_sums(theta, phi, up, pi))
            for c, b in up_val.items():
                s.add(up[c] == b)
            for r in ROWS:
                cons, _ = row_score_constraints(
                    theta, pi, phi, r, n, ('>=', 3) if r == 'h' else 2)
                s.add(*cons)
            s.add(*anchor_score_constraints(theta, pi, n))
            if s.check() == sat:
                sat_leaves.append(up_val)
            else:
                n_unsat += 1
        if sat_leaves:
            results['SAT'].append(cid)
            for uv in sat_leaves:
                eo = sorted((x, y) if b else (y, x)
                            for (x, y), b in uv.items())
                sat_dump.append(dict(
                    class_id=cid,
                    orientation=[f'{a}->{b}' for a, b in eo],
                    edges=cls['edges'], types=cls['types'],
                    sinks=cls['sinks']))
        else:
            results['UNSAT'].append(cid)
    print(f"n={n}: UNSAT classes={len(results['UNSAT'])} "
          f"SAT classes={len(results['SAT'])}")
    for cid in results['SAT']:
        print('  SAT:', cid)
    with open('R3_CLASS_SAT_LEAVES.json', 'w') as f:
        json.dump(sat_dump, f, indent=1)


if __name__ == "__main__":
    main()
