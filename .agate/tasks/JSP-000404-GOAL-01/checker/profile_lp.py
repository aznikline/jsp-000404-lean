"""LP/integer reconstruction of Sendov Lemma 4.1 at the cell level.

Convex-position model: s centers, fan order at i is i+1..i+s-1 (mod s).
Cells m_{i,r} = floor(u*phi/2). Constraints are integer-relaxations of the
angle constraints, so the integer optimum is an upper bound on the true max.
If it still meets the Sendov cap, the constraint set is complete enough.
"""

import itertools
import sys

def fan_pos(v, w, s):
    return (w - v) % s

def per_vertex_profiles(s, n):
    out = []
    for ints_ in itertools.product(range(n), repeat=s - 2):
        if sum(ints_) > n - 1:
            continue
        for me in range(1, n + 1):
            tot = sum(ints_) + me
            if tot > n or tot < n - s + 2:
                continue
            k = sum(max(m - 1, 0) for m in ints_) + (me - 1)
            out.append((ints_, me, k))
    return out

def block_cells(ints_, lo, hi):
    return sum(ints_[lo - 1:hi - 1])

def max_F(s, n, delta):
    import math
    E = math.floor(2 * (n + delta))            # exterior budget: sum e_i = 2
    I = math.floor((s - 2) * (n + delta))      # interior budget: sum int_i = s-2
    profs = per_vertex_profiles(s, n)
    tris = []
    for (a, b, c) in itertools.combinations(range(s), 3):
        tb = []
        for (v, j, k) in ((a, b, c), (b, a, c), (c, a, b)):
            lo, hi = sorted((fan_pos(v, j, s), fan_pos(v, k, s)))
            tb.append((v, lo, hi))
        tris.append(tb)
    # group triangle constraints by their max vertex index (checkable when
    # that vertex gets assigned)
    tri_at = [[] for _ in range(s)]
    for tb in tris:
        mx = max(v for (v, _, _) in tb)
        tri_at[mx].append(tb)

    best = [0, None]
    assign = [None] * s
    mes = [0] * s
    mints = [0] * s

    def rec(i):
        if i == s:
            F = sum(1 << k for (_, _, k) in assign)
            if F > best[0]:
                best[0] = F
                best[1] = [(iv, me, k) for (iv, me, k) in assign]
            return
        for prof in profs:
            ints_, me, k = prof
            if sum(mes[:i]) + me + (s - i - 1) > E:
                continue
            if sum(mints[:i]) + sum(ints_) > I:
                continue
            assign[i] = prof
            ok = True
            for tb in tri_at[i]:
                tot = 0
                for (v, lo, hi) in tb:
                    tot += block_cells(assign[v][0], lo, hi)
                if tot > n:
                    ok = False
                    break
            if ok:
                mes[i] = me
                mints[i] = sum(ints_)
                rec(i + 1)
                mes[i] = 0
                mints[i] = 0
            assign[i] = None
    rec(0)
    return best

def sendov_cap(n, delta):
    return (1 << n) + ((1 << (n - 2)) if delta >= 0.5 else 0)

if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "34"
    ss = (3, 4) if which == "34" else (int(which),)
    for s in ss:
        for n in range(s, 9):
            for d in (0.2, 0.7):
                F, _ = max_F(s, n, d)
                cap = sendov_cap(n, d)
                flag = "OK" if F <= cap else "!!! EXCEEDS CAP"
                print(f"s={s} n={n} d={d}:  F*={F}  cap={cap}  {flag}",
                      flush=True)
