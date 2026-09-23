#!/usr/bin/env python3
# tools/certb_scan.py — skeleton-driven recognizer for
# `signed_chain_certB` (Jsp000404/K3bGeometry.lean).
#
# certB hypotheses on the skeleton (chain x = [i0] + oi0[p+1..p+L+1]):
#
#   per piece j = 1..L (Lean index i = j-1 ∈ range L):
#     hbA:  side_{x0}(x_j, x_{j+1})   = +1
#           (∠(x_j,x_0,x_{j+1}) = dirArc(x0, x_j, x_{j+1}))
#     hbT:  side_{x_j}(x_0, x_{j+1})  = −1
#           (∠(x_0,x_j,x_{j+1}) = π − dirArc(x_j, x_0, x_{j+1}))
#     hbS:  side_{x_{j+1}}(x_0, x_j)  = +1
#           (∠(x_0,x_{j+1},x_j) = dirArc(x_{j+1}, x_0, x_j))
#     hsplit: dirArc(x_j, x_0, x_{j-1}) ≤ dirArc(x_j, x_0, x_{j+1})
#           (x_{j-1} on the forward arc x_0 → x_{j+1} at row x_j;
#            automatic for j = 1 since dirArc(·,x_0,x_0) = 0)
#     demand: D_j = dirArc(x_j, x_{j-1}, x_{j+1}) ≥ m_j·λ where
#           m_j = max(q_j, 1) if side_{x_j}(x_{j-1}, x_{j+1}) = −1
#           (complement branch: ∠ = π − D_j ≤ π − λ gives D_j ≥ λ),
#           else m_j = q_j (qs baseline only).
#           Budgets combine by MAX, not addition: D ≥ qλ and D ≥ λ
#           give D ≥ max(q,1)·λ.
#   hfanL: chain occupies consecutive positions of order[x0] (built in
#          by enumeration) and the wrap gap closes the fan.
#   hcomp: dirArc(x_{L+1}, x_0, x_L) + dirArc(x_{L+1}, x_L, x_0) = π —
#          automatic for distinct dirReps (distinct positions in
#          order[x_{L+1}]).
#   left boundary  H_0 = dirArc(x0, x_{L+1}, x_1) ≥ a·λ:
#          baseline = qs-sum of the wrap arc; bonus +1 iff
#          side_{x0}(x_1, x_{L+1}) = +1 (∠ = span ≤ π−λ ⇒ wrap ≥ λ).
#   right boundary H'_L = dirArc(x_{L+1}, x_L, x_0) ≥ b·λ:
#          baseline = qs-sum of that arc; bonus +1 iff
#          side_{x_{L+1}}(x_0, x_L) = +1 (∠(x_0→x_L) = S_{L+1} ≤ π−λ
#          ⇒ H'_L = π − S_{L+1} ≥ λ).
#
#   σ = a + b + Σ m_j − 2n  (integer score; negative allowed);
#   δ ≥ σ/2,  low target σ ≥ 1, high target σ ≥ 2.
#
# Direction decode (mandate §4A): the sign of oangle(u→v) at row r is
#   side(u,v) = (+1 if pos(v) > pos(u) else −1), flipped when the lift
#   bits of u,v differ.  Bits alone do NOT determine the sign — the
#   local cut position enters through pos.  side is invariant under
#   the gauge transform "rotate cut + flip the crossing ray's bit";
#   bits-only comparisons are not.  See the leaf_0002 regression in
#   `rotate_regression`.
#
# Diagnostic only — no certificate produced; the hypotheses are the
# geometric content certB consumes.

import glob
import json
import os
import sys

from fractions import Fraction as F


def load(dpath):
    for f in sorted(glob.glob(os.path.join(dpath, 'leaf_*.json'))):
        yield os.path.basename(f), json.load(open(f, encoding='utf-8'))


def pos_map(order):
    return {v: k for k, v in enumerate(order)}


def side_of(skel_row, u, v):
    """Sign of oangle(ray→u, ray→v) at this row.

    +1 ⇒ ∠(u,row,v) = dirArc(row, u, v)  (forward arc u → v);
    −1 ⇒ ∠(u,row,v) = π − dirArc(row, u, v).
    """
    pm = pos_map(skel_row['order'])
    bits = skel_row['bits']
    sgn = 1 if pm[v] > pm[u] else -1
    if bits[str(u)] != bits[str(v)]:
        sgn = -sgn
    return sgn


def arc_qs(skel_row, u, v):
    """Baseline cell count of dirArc(row, u, v): sum of qs over the
    gaps of the forward arc u -> v in this row's order; None if u == v
    or either is absent."""
    order = skel_row['order']
    qs = skel_row['qs']
    pm = pos_map(order)
    if u not in pm or v not in pm or u == v:
        return None
    pu, pv = pm[u], pm[v]
    ln = len(order)
    total = 0
    k = pu
    while k != pv:
        total += qs[k]
        k = (k + 1) % ln
    return total


def scan_leaf(d):
    """Best certB score over all (i0, p, L).  Returns list of hits."""
    s = d['s']
    skel = {e['v']: e for e in d['skeleton']}
    n = d['n']
    hits = []
    for i0 in range(s):
        oi0 = skel[i0]['order']
        ln = len(oi0)
        for p in range(ln):
            for L in range(2, ln):
                x = [i0] + [oi0[(p + j) % ln] for j in range(L + 1)]
                if len(set(x)) != L + 2:
                    continue
                ok = True
                ms = []
                for j in range(1, L + 1):
                    xj, xjm, xjp = x[j], x[j - 1], x[j + 1]
                    # hbA: side_{x0}(x_j, x_{j+1}) = +1
                    if side_of(skel[i0], xj, xjp) != 1:
                        ok = False
                        break
                    # hbT: side_{x_j}(x_0, x_{j+1}) = −1
                    if side_of(skel[xj], i0, xjp) != -1:
                        ok = False
                        break
                    # hbS: side_{x_{j+1}}(x_0, x_j) = +1
                    if side_of(skel[xjp], i0, xj) != 1:
                        ok = False
                        break
                    # hsplit: x_{j-1} on the forward arc x_0 → x_{j+1}
                    # at row x_j (automatic for j = 1)
                    if j >= 2:
                        pmj = pos_map(skel[xj]['order'])
                        mj = len(skel[xj]['order'])
                        p0, pm_, pp = pmj[i0], pmj[xjm], pmj[xjp]
                        if (pm_ - p0) % mj > (pp - p0) % mj:
                            ok = False
                            break
                    # demand bound: baseline + complement bonus (max)
                    q = arc_qs(skel[xj], xjm, xjp)
                    if q is None:
                        ok = False
                        break
                    demand = side_of(skel[xj], xjm, xjp) == -1
                    ms.append(max(q, 1) if demand else q)
                if not ok:
                    continue
                a = arc_qs(skel[i0], x[L + 1], x[1])
                b = arc_qs(skel[x[L + 1]], x[L], i0)
                if a is None or b is None:
                    continue
                # cap bonuses (see header): ∠ ≤ π−λ on the arc branch
                # bounds the complementary wrap below by λ.
                if side_of(skel[i0], x[1], x[L + 1]) == 1:
                    a = max(a, 1)
                if side_of(skel[x[L + 1]], i0, x[L]) == 1:
                    b = max(b, 1)
                sigma = a + b + sum(ms) - 2 * n
                hits.append((sigma, i0, p, L, x, a, b, ms))
    return hits


def rotate_row_cut(row):
    """Equivalent representation: rotate the local cut of `row` by one
    position (order/qs rotate; the ray crossing the cut gets its lift
    bit flipped).  Preserves all side() signs; changes bare bit
    comparisons involving the moved ray."""
    order = row['order']
    qs = row['qs']
    bits = dict(row['bits'])
    moved = order[0]
    bits[str(moved)] = 1 - bits[str(moved)]
    return {'v': row['v'], 'order': order[1:] + [order[0]],
            'qs': qs[1:] + [qs[0]], 'bits': bits}


def rotate_regression(dpath, leaf='leaf_0002.json', row_v=0):
    """leaf_0002 regression (mandate §4B): the certB bundle
    x=[0,1,2,3,4,5], L=4, a=b=1, m=(1,1,1,1), σ=2 must survive a
    gauge-equivalent cut rotation of row `row_v`.  A bits-only decode
    is not gauge-invariant and drops the bundle."""
    d = json.load(open(os.path.join(dpath, leaf), encoding='utf-8'))
    skel = {e['v']: e for e in d['skeleton']}
    rot = rotate_row_cut(skel[row_v])
    # bits-only probes that the old decoder used:
    b0, b0r = skel[row_v]['bits'], rot['bits']
    probes = {}
    for pair in [(1, 2), (2, 3), (3, 4), (4, 5)]:
        u, v = pair
        probes[f'bits_eq({u},{v})'] = (
            b0[str(u)] == b0[str(v)], b0r[str(u)] == b0r[str(v)])
        probes[f'side({u},{v})'] = (
            side_of(skel[row_v], u, v), side_of(rot, u, v))
    return d, rot, probes


def main():
    for dpath in sys.argv[1:]:
        total = cov = 0
        dist = {}
        for name, d in load(dpath):
            total += 1
            tau = F(str(d['target_tau']))
            hits = scan_leaf(d)
            best = max(hits, key=lambda h: h[0]) if hits else None
            if best is not None:
                dist[best[0]] = dist.get(best[0], 0) + 1
            if best is not None and best[0] >= 2 * tau:
                cov += 1
        print(f'{dpath}: leaves={total} certB-covered={cov} '
              f'best-sigma-dist={dict(sorted(dist.items()))}')


if __name__ == '__main__':
    main()
