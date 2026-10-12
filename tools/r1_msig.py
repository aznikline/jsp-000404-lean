#!/usr/bin/env python3
"""R1 class-free multiset signatures — shared-successor strong form.

For each cyclic predecessor p (None = bottom end, or a chord x of the
row) we introduce ONE shared real `sp_p` — its successor element — with

  p = None :  sp ∈ S  ∧  ∀z: sp ≤ z                       (min chord)
  p = x    :  Or( x<sp ∧ sp∈S ∧ ∀z(z≤x∨sp≤z),             # witness
                  sp = t_i+p ∧ ∀z z≤x )                   # wrap

All signature components are then ATOMIC ors on the sp-vars:
  band(p,lo,hi)  =  lo <= sp_p - base_p < hi
  (base_None = t_i, base_x = x)

The successor-position enumeration (mem) and neighbor conditions live
inside the `spd` ors as lazy sub-ors — only split if the core needs.

Component ors per signature:
  s0: ∀p band(p,0,2)
  s1: ∀p Or(b02,b23) ;  ex Or_p b23 ;  b2 ∀pairs Or(bx02,by02)
  s2: ∀p Or(b02,b23,b34) ;  b2 ∀triples Or(bx02,by02,bu02) ;
      b3 ∀pairs Or(bx0-3,by0-3) ;  ex Or_p b2-4 ;
      pat Or_p b3-4  or  Or_pairs And(b2-4,b2-4)
"""
import z3, itertools, sys, os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s7_canon import build, nb


def band(sp, base, lo, hi):
    return z3.And(lo <= sp - base, sp - base < hi)


def msig_ors(t_i, S, pv, kind, rowtag='r'):
    """Shared-succ or-list for one row.  Returns [(tag,pred,expr)] with
    the per-pred `spd` ors FIRST."""
    preds = [None] + list(S)
    sp = {}
    base = {}
    ors = []
    for k, pr in enumerate(preds):
        v = z3.Real(f'sp_{rowtag}_{k}')
        sp[pr] = v
        base[pr] = t_i if pr is None else pr
        if pr is None:
            ors.append(('spd', pr, z3.And(
                z3.Or(*[v == z for z in S]),
                z3.And(*[v <= z for z in S]))))
        else:
            ors.append(('spd', pr, z3.Or(
                z3.And(pr < v, z3.Or(*[v == z for z in S]),
                       z3.And(*[z3.Or(z <= pr, v <= z) for z in S])),
                z3.And(v == t_i + pv,
                       z3.And(*[z <= pr for z in S])))))
        # implied aggregate bounds (sound: implied by spd + corridors)
        ors.append(('gb', pr,
                    z3.And(t_i <= v, v <= t_i + pv)))
    # global invariant: cyclic gaps partition the span -> Σ gaps = pv
    # (true for any real row: succ is a bijection preds ↔ S ∪ {T})
    ors.append(('gsum', None,
                sum(sp[p] - base[p] for p in preds) == pv))
    b = lambda p, lo, hi: band(sp[p], base[p], lo, hi)
    if kind == 's0':
        ors += [('g', p, b(p, 0, 2)) for p in preds]
    elif kind == 's1':
        ors += [('g', p, z3.Or(b(p, 0, 2), b(p, 2, 3))) for p in preds]
        ors.append(('ex', None, z3.Or(*[b(p, 2, 3) for p in preds])))
        ors += [('b2', (x, y), z3.Or(b(x, 0, 2), b(y, 0, 2)))
                for x, y in itertools.combinations(preds, 2)]
    elif kind == 's2':
        ors += [('g', p, z3.Or(b(p, 0, 2), b(p, 2, 3), b(p, 3, 4)))
                for p in preds]
        ors += [('b2', (x, y, u),
                 z3.Or(b(x, 0, 2), b(y, 0, 2), b(u, 0, 2)))
                for x, y, u in itertools.combinations(preds, 3)]
        ors += [('b3', (x, y),
                 z3.Or(z3.And(sp[x] - base[x] < 3),
                       z3.And(sp[y] - base[y] < 3)))
                for x, y in itertools.combinations(preds, 2)]
        ors.append(('ex', None, z3.Or(
            *[z3.Or(b(p, 2, 3), b(p, 3, 4)) for p in preds])))
        ors.append(('pat', None, z3.Or(
            *[b(p, 3, 4) for p in preds],
            *[z3.And(z3.Or(b(p, 2, 3), b(p, 3, 4)),
                     z3.Or(b(q, 2, 3), b(q, 3, 4)))
              for p, q in itertools.combinations(preds, 2)])))
    else:
        raise ValueError(kind)
    return ors


def build_solver(P, spec):
    """spec = [(rank, kind)] -> solver (sanity/sat checking only)."""
    delta, t, d, D, p, base_, trips = build(P)
    s = z3.Solver()
    s.add(base_)
    for tr in trips.values():
        s.add(tr)
    for r, kind in spec:
        S = [D(r, j) for j in range(P) if j != r]
        for tag, pred, e in msig_ors(t[r], S, p, kind):
            s.add(e)
    return s
