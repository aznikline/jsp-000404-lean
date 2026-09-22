"""Classify consistent PAIRS of saturated vertex variants.

A saturated vertex variant (k = n-1): qs = perm of (n,0,...,0),
B_v = 0.  Its 'mode' is determined by (order, bits, position of the
big gap):

  cap    : some direct arc contains the big gap (q_arc = n)
  charge : some comp arc avoids the big gap (q_arc = 0, gain 1)
  F1     : bits all equal, big = wrap gap (position s-1 in order)
  F2     : bits (0,1), big = middle gap
  F3     : bits (1,1), big = first gap

For s=4: two saturated vertices x,y + two others u,w.  Edge (x,y)
side-consistency: side_x[(y,k)] = -side_y[(x,k)] for k in {u,w}.

We enumerate all (var_x, var_y) variant pairs (order, bits, big-gap
position), check edge consistency for each choice of which roles
u,w play, and tally the mode pairs that are consistent.  Then for
each consistent pair-mode we ask what the triangle equalities
{x,y,u}, {x,y,w} force.
"""
import sys, itertools
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_model as gm
import generic_enum as ge

N = S = 4

# All saturated variants at vertex 0 (as "x") and vertex 1 ("y"):
# build_VV for k=3 gives variants over 'others' = remaining vertices.
# A pair (x-var at vertex X, y-var at vertex Y) is edge-consistent
# iff for both third vertices k: side_x[(Y,k)] == -side_y[(X,k)].


def sat_variants(v, n=4, s=4):
    others = tuple(x for x in range(s) if x != v)
    return [vv for vv in
            gm.vertex_variants(v, n - 1, others, n)]


def mode_of(vv):
    """Return (mode, detail) for a saturated variant dict."""
    n = 4
    order = vv['order']
    bits = vv['bits']
    qs = vv['qs']
    big = qs.index(n)
    b2, b3 = bits[order[1]], bits[order[2]]
    pos = {d: i for i, d in enumerate(order)}
    # arcs between consecutive-position direction pairs
    # gap t lies between order[t] and order[t+1 mod m]
    arcss = {(order[0], order[1]): frozenset([0]),
             (order[1], order[2]): frozenset([1]),
             (order[0], order[2]): frozenset([0, 1])}
    def comp(u, w):
        return bits[u] != bits[w]
    for (u, w), arc in arcss.items():
        if not comp(u, w) and sum(qs[g] for g in arc) >= n:
            return 'cap'
    for (u, w), arc in arcss.items():
        if comp(u, w) and sum(qs[g] for g in arc) == 0:
            return 'charge'
    if (b2, b3) == (0, 0):
        return 'F1'
    if (b2, b3) == (0, 1):
        return 'F2'
    return 'F3'


def main():
    X, Y = 0, 1
    others_xy = [v for v in range(S) if v not in (X, Y)]
    VX = sat_variants(X)
    VY = sat_variants(Y)
    print(f'sat variants: |VX|={len(VX)} |VY|={len(VY)}')
    modecount = {}
    paircount = {}
    examples = {}
    for vx in VX:
        mx = mode_of(vx)
        modecount[mx] = modecount.get(mx, 0) + 1
        for vy in VY:
            ok = all(vx['side'][(Y, k)] == -vy['side'][(X, k)]
                     for k in others_xy)
            if not ok:
                continue
            my = mode_of(vy)
            key = tuple(sorted((mx, my)))
            paircount[key] = paircount.get(key, 0) + 1
            examples.setdefault(key, []).append((vx, vy))
    print('mode counts:', modecount)
    print('consistent pair modes:')
    for k, c in sorted(paircount.items()):
        print(f'  {k}: {c} pairs')
    # For each failing-failing pair, print the structural relation
    for key, exs in examples.items():
        if not all(m.startswith('F') for m in key):
            continue
        print(f'=== {key} example:')
        vx, vy = exs[0]
        for name, vv in (('x', vx), ('y', vy)):
            print(f'  {name}: order={vv["order"]} bits='
                  f'{dict(sorted(vv["bits"].items()))} qs={vv["qs"]} '
                  f'mode={mode_of(vv)}')
        # which positions do X,Y occupy in each other's order
        print('  pos_x[y]=', vx['order'].index(Y),
              'pos_y[x]=', vy['order'].index(X))
        print('  side_x:', {k: vx['side'][(Y, k)] for k in others_xy},
              ' side_y:', {k: vy['side'][(X, k)] for k in others_xy})


if __name__ == '__main__':
    main()
