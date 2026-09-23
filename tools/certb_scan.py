#!/usr/bin/env python3
# tools/certb_scan.py — skeleton-driven recognizer for signed_chain_certB.
#
# certB hypotheses on the skeleton (chain x = [i0, oi0[p+1..p+L+1]]):
#   pieces j=1..L: apex-x0 arc needs bits[i0][x_j] == bits[i0][x_{j+1}];
#     apex-x_j complement needs bits[x_j][x0] != bits[x_j][x_{j+1}];
#     apex-x_{j+1} arc needs bits[x_{j+1}][x0] == bits[x_{j+1}][x_j];
#     for j >= 2 a split pos_{x_j}(x_{j-1}) <= pos_{x_j}(x_{j+1})
#     counting forward from pos(x0) in order[x_j].
#   demands D_j = dirArc(x_j, x_{j-1}, x_{j+1}): bound m_j = q_j + 1
#     if the demand angle bits differ (complement branch, giving one
#     extra cell on top of the q baseline), else m_j = q_j.
#     Here q_j = qs[x_j][gap of (x_{j-1} -> x_{j+1})] when that arc is
#     a single gap in order[x_j]; if the demand arc spans several gaps
#     the baseline is the sum over them.
#   left boundary a = qs[i0][wrap gap x_{L+1} -> x_1].
#   right boundary b' = qs[x_{L+1}][gap x_L -> x0] if adjacent there
#     (wrap), else the arc sum baseline.
#   sigma = a + b' + sum m_j - 2n ; delta >= sigma/2.
#
# Reports, per leaf, the best (i0, p, L) and whether sigma >= 2*tau.
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


def arc_qs(skel_row, u, v):
    """Baseline cell count of dirArc(v_row, u, v): sum of qs over the
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
        pm0 = pos_map(oi0)
        b0 = skel[i0]['bits']
        for p in range(ln):
            for L in range(2, ln):
                x = [i0] + [oi0[(p + j) % ln] for j in range(L + 1)]
                if len(set(x)) != L + 2:
                    continue
                # per-piece checks
                ok = True
                ms = []
                for j in range(1, L + 1):
                    xj, xjm, xjp = x[j], x[j - 1], x[j + 1]
                    bj = skel[xj]['bits']
                    bjp = skel[xjp]['bits']
                    # apex-x0 arc branch
                    if b0[str(xj)] != b0[str(xjp)]:
                        ok = False
                        break
                    # apex-xj complement branch
                    if bj[str(i0)] == bj[str(xjp)]:
                        ok = False
                        break
                    # apex-xjp arc branch
                    if bjp[str(i0)] != bjp[str(xj)]:
                        ok = False
                        break
                    # split for j >= 2: pos(x_{j-1}) <= pos(x_{j+1})
                    # forward from pos(x0) in order[x_j]
                    if j >= 2:
                        pmj = pos_map(skel[xj]['order'])
                        p0, pm_, pp = pmj[i0], pmj[xjm], pmj[xjp]
                        forward = (pm_ - p0) % ln <= (pp - p0) % ln
                        if not forward:
                            ok = False
                            break
                    # demand bound: q_baseline + 1 if demand bits differ
                    q = arc_qs(skel[xj], xjm, xjp)
                    if q is None:
                        ok = False
                        break
                    demand = bj[str(xjm)] != bj[str(xjp)]
                    ms.append(max(q, 1) if demand else q)
                if not ok:
                    continue
                # boundaries — baseline qs plus the cap bonus: same
                # bits at (x0; x1, x_{L+1}) gives ∠ = dirArc(x0,x1,xL+1)
                # <= pi - lam (triAngle), hence the wrap H_0 >= lam;
                # same bits at (x_{L+1}; x0, x_L) caps S_{L+1}, hence
                # H'_L = pi - S_{L+1} >= lam.
                a = arc_qs(skel[i0], x[L + 1], x[1])
                b = arc_qs(skel[x[L + 1]], x[L], i0)
                if a is None or b is None:
                    continue
                bL = skel[x[L + 1]]['bits']
                if b0[str(x[1])] == b0[str(x[L + 1])]:
                    a = max(a, 1)
                if bL[str(i0)] == bL[str(x[L])]:
                    b = max(b, 1)
                sigma = a + b + sum(ms) - 2 * n
                hits.append((sigma, i0, p, L, x, a, b, ms))
    return hits


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
