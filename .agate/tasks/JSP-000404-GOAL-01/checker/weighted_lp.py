"""Decisive experiment: do triangle-debt necessary conditions + cell bounds
imply the weighted cap?

Model (convex position, s centers, lam = 2pi/u, u = 2n+2d):
  gaps at v: interior g_1..g_{s-2} + exterior e. cells m = floor(angle/lam).
  per-vertex: sum_g m <= n (since sum angles = pi = (n+d)lam)
  interior angle <= 1-2/u -> every contiguous interior block: cells <= n-1
  exterior e >= 2/u -> m_e >= 1
  triangle {a,b,c}: block cells sum <= n (interior angle <= 1-2/u gives
    <= n-1 actually; keep <= n-1 via blocks)  -- we use block bounds
  polygon interior sum: sum_v int_v = s-2 -> sum interior cells <= floor((s-2)(n+d))

Remainder necessary conditions (Farkas family):
  for each triangle subset S:  sum_{T in S} D_T <= sum_v pay(v,S)
    D_T = n+d - C_T (remainder demand, exact triangle sum)
    pay(v,S) = greedy: sum_{g in int(v)} cnt_S(g) r_g <= f(B_v, cnts),
      B_v = n+d - C_v (exact vertex remainder), 0<=r<=1.

If max F over cell assignments satisfying all these conditions == cap,
the closed-form certificate family is COMPLETE for the weighted bound.
"""

import itertools
import sys
from fractions import Fraction as Fr

def per_vertex_options(s, n):
    """all (ints tuple len s-2, me) with sum(ints)<=n-1, 1<=me<=n,
    and every contiguous interior block cells <= n-1 (auto since sum<=n-1)."""
    out = []
    for ints_ in itertools.product(range(n), repeat=s - 2):
        if sum(ints_) > n - 1:
            continue
        for me in range(1, n + 1):
            tot = sum(ints_) + me
            if tot > n:
                continue
            k = sum(max(m - 1, 0) for m in ints_) + (me - 1)
            out.append((ints_ + (me,), k))
    return out

def blocks_of(v, j, k, s):
    """interior gap indices (0..s-3) of the block at v between dirs to j,k."""
    pj, pk = (j - v) % s, (k - v) % s
    lo, hi = min(pj, pk), max(pj, pk)
    return list(range(lo - 1, hi - 1))

def tri_blocks(assign_v, v, j, k, s):
    return sum(assign_v[g] for g in blocks_of(v, j, k, s))

def greedy_pay(B, cnts, delta):
    """max sum cnt*r s.t. sum r <= B (=b0+b1*d), 0<=r<=1. Piecewise in d;
    evaluate numerically at delta (Fraction)."""
    Bv = B[0] + B[1] * delta
    tot = Fr(0); rem = Bv
    for c in sorted(cnts, reverse=True):
        if c == 0 or rem <= 0:
            break
        take = min(Fr(1), rem)
        tot += c * take; rem -= take
    return tot

def debt_ok(assign, n, delta, s):
    """check all triangle-subset remainder-debt conditions."""
    tris = list(itertools.combinations(range(s), 3))
    infos = []
    for (a, b, c) in tris:
        inc, C = [], 0
        for (v, j, k) in ((a, b, c), (b, a, c), (c, a, b)):
            for g in blocks_of(v, j, k, s):
                inc.append((v, g)); C += assign[v][g]
        infos.append((inc, C))
    Bv = [n + delta - sum(assign[v]) for v in range(s)]  # numeric Fraction
    # subsets: cap 2^len(tris); for s<=6 len<=20 too many -> limit size <=4?
    # For s=4: len=4; s=5: 10 -> 1024 subsets ok; s=6: 20 -> use size<=3
    maxS = {4: 4, 5: 4, 6: 3}.get(s, 3)
    for r_ in range(1, maxS + 1):
        for S in itertools.combinations(range(len(tris)), r_):
            need = sum(n + delta - infos[t][1] for t in S)
            cap = Fr(0)
            for v in range(s):
                cnts = [sum(1 for t in S if (v, g) in infos[t][0])
                        for g in range(s - 2)]
                rem = Bv[v]
                for c in sorted(cnts, reverse=True):
                    if c == 0 or rem <= 0:
                        break
                    take = min(Fr(1), rem)
                    cap += c * take; rem -= take
            if need > cap:
                return False, (S, need, cap)
    return True, None

def int_constraints_ok(assign, n, delta, s, upto=None):
    """integer-model checks over vertices [0, upto): interior block cells
    <= n-1 per triangle block, triangle cell sums <= n, exterior budget."""
    V = range(s) if upto is None else range(upto)
    for (a, b, c) in itertools.combinations(list(V), 3):
        tot = 0
        for (v, j, k) in ((a, b, c), (b, a, c), (c, a, b)):
            tot += tri_blocks(assign[v], v, j, k, s)
        for (v, j, k) in ((a, b, c), (b, a, c), (c, a, b)):
            if tri_blocks(assign[v], v, j, k, s) > n - 1:
                return False
        if tot > n:
            return False
    # exterior budget: sum_v m_e <= floor(2(n+d))  (sum of exterior arcs = 2pi)
    if upto is None:
        if sum(assign[v][s - 2] for v in range(s)) > int(2 * (n + delta)):
            return False
        if sum(sum(assign[v][g] for g in range(s - 2)) for v in range(s)) \
                > int((s - 2) * (n + delta)):
            return False
    return True

def run(s, n, delta, cap):
    opts = sorted(per_vertex_options(s, n), key=lambda x: -x[1])
    best = 0; bestw = None
    best_cond = 0; bestw_cond = None
    count = 0
    assign = [None] * s
    Fpart = 0
    exceeded = []   # debt-satisfying assignments beating cap

    def dfs(v, kmax):
        nonlocal best, bestw, best_cond, bestw_cond, count, Fpart
        if not int_constraints_ok(assign, n, delta, s, upto=v):
            return
        # F-bound prune vs cap: subtree can't beat cap at all
        if best_cond >= cap and best >= cap \
                and Fpart + (s - v) * (1 << kmax) <= cap:
            return
        if v == s:
            count += 1
            if not int_constraints_ok(assign, n, delta, s):
                return
            if Fpart > best:
                best, bestw = Fpart, [tuple(a) for a in assign]
            if Fpart <= cap and Fpart <= best_cond:
                return  # only care about violations / new maxima
            ok, wit = debt_ok(assign, n, delta, s)
            if ok:
                if Fpart > best_cond:
                    best_cond, bestw_cond = Fpart, [tuple(a) for a in assign]
                if Fpart > cap:
                    exceeded.append(([tuple(a) for a in assign], Fpart))
            return
        for (cells, k) in opts:
            if v > 0 and k > kmax:
                break   # cyclic symmetry: v0 is a max-k vertex
            assign[v] = cells
            Fpart += 1 << k
            dfs(v + 1, k if v == 0 else kmax)
            Fpart -= 1 << k
        assign[v] = None
    dfs(0, n - 1)
    return best, bestw, best_cond, bestw_cond, count, exceeded

if __name__ == "__main__":
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    dn = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    dd = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    delta = Fr(dn, dd)
    cap = (1 << n) if delta < Fr(1, 2) else (1 << n) + (1 << (n - 2))
    best, bw, bestc, bwc, cnt, exceeded = run(s, n, delta, cap)
    print(f"s={s} n={n} d={delta}: leaf-visits={cnt}")
    print(f"  maxF(int model)      = {best}   {bw}")
    print(f"  maxF(+debt conds)    = {bestc}   {bwc}")
    print(f"  cap                  = {cap}")
    print("  " + ("GO: debt conds close the gap" if bestc <= cap
                    else f"GAP remains: {bestc} > {cap}"))
    for (w, F) in exceeded[:10]:
        print(f"    VIOLATION F={F}: {w}")
