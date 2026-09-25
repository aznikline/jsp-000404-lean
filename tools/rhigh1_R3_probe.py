#!/usr/bin/env python3
"""Float probe: search real five-point configs in the R-HIGH1 regime
(unique defect-1 row, all other rows defect >= 2, n >= 3,
delta = pi/lam - n in [1/2, 1)) for R = #(defect-2 non-anchor rows) >= 3.

Row data are chart-independent (cyclic gaps of chord directions mod pi).
Legality: every triangle angle <= pi - lam.  Float only -- any hit must
be re-verified exactly before being trusted.

usage: python tools/rhigh1_R3_probe.py [iters] [seed]
"""
import math, random, sys, itertools, json

EPS = 1e-9


def tri_max_angle(P):
    m = 0.0
    for a, b, c in itertools.combinations(range(len(P)), 3):
        for x, y, z in ((a, b, c), (b, a, c), (c, a, b)):
            ux, uy = P[y][0] - P[x][0], P[y][1] - P[x][1]
            vx, vy = P[z][0] - P[x][0], P[z][1] - P[x][1]
            d = math.hypot(ux, uy) * math.hypot(vx, vy)
            if d < 1e-12:
                return math.pi
            m = max(m, math.acos(max(-1, min(1, (ux * vx + uy * vy) / d))))
    return m


def row_data(P, w, lam, n):
    dirs = sorted(math.atan2(P[j][1] - P[w][1], P[j][0] - P[w][0]) % math.pi
                  for j in range(len(P)) if j != w)
    m = len(dirs)
    gaps = [(dirs[(t + 1) % m] - dirs[t]) % math.pi for t in range(m)]
    gaps[-1] = math.pi - sum(gaps[:-1])
    # reject near-threshold gaps (float ambiguity)
    for g in gaps:
        r = g / lam
        if abs(r - round(r)) < 1e-7:
            return None
    cells = sum(int(math.floor(g / lam)) for g in gaps)
    big = sum(1 for g in gaps if g >= lam)
    return big + n - cells, big, cells, gaps


def classify(P, lam):
    n = int(math.floor(math.pi / lam))
    rows = []
    for w in range(len(P)):
        r = row_data(P, w, lam, n)
        if r is None:
            return None
        rows.append(r)
    return n, rows


def score(P, lam):
    """Return (R, info) if R-HIGH1 holds, else None."""
    c = classify(P, lam)
    if c is None:
        return None
    n, rows = c
    defs = [r[0] for r in rows]
    if defs.count(1) != 1 or min(defs) < 1:
        return None
    if any(d < 2 for i, d in enumerate(defs) if d != 1):
        return None
    return defs.count(2), n, defs, rows


def lam_choices(P):
    amax = tri_max_angle(P)
    cap = math.pi - amax
    out = []
    for n in range(3, 8):
        for frac in [0.5 + 0.02 * k for k in range(25)]:
            lam = math.pi / (n + frac)
            if lam <= cap - 1e-9:
                out.append(lam)
    return out


def best(P):
    top = None
    for lam in lam_choices(P):
        s = score(P, lam)
        if s is not None and (top is None or s[0] > top[0][0]):
            top = (s, lam)
    return top


def main():
    iters = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    hist = {}
    hits = []
    seed = [(5, -4), (2, -5), (5, -2), (-5, 10), (1, -10)]
    for it in range(iters):
        if it % 2 == 0:
            P = [(x + rng.gauss(0, 1.0), y + rng.gauss(0, 1.0))
                 for x, y in seed]
        else:
            P = [(rng.uniform(-10, 10), rng.uniform(-10, 10))
                 for _ in range(5)]
        b = best(P)
        cur = b[0][0] if b else -1
        # hill-climb toward larger R
        for k in range(150):
            sig = 0.8 if k < 75 else 0.2
            Q = [(x + rng.gauss(0, sig), y + rng.gauss(0, sig)) for x, y in P]
            bq = best(Q)
            cq = bq[0][0] if bq else -1
            if cq >= cur:
                P, b, cur = Q, bq, cq
        hist[cur] = hist.get(cur, 0) + 1
        if cur >= 3:
            (R, n, defs, rows), lam = b
            hits.append({"P": P, "lam": lam, "n": n, "R": R, "defs": defs,
                         "gaps_over_lam": [[g / lam for g in r[3]]
                                           for r in rows]})
            if len(hits) >= 5:
                break
    print("R histogram (R-HIGH1 configs, -1 = regime not reached):", hist)
    print("hits R>=3:", len(hits))
    for h in hits:
        print(json.dumps(h))


if __name__ == "__main__":
    main()
