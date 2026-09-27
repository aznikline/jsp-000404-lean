#!/usr/bin/env python3
"""Exact (Fraction) regression for Jsp000404/StarReceiver.lean.

Units of lambda.  beta = delta, pi = n + delta.
1. Packet local example: n=4, delta=3/4, receiver gaps
   (11/10, 1/10, 47/20, 6/5) -> floors (1,0,2,1), cells 4, big 3, c=3.
2. Grid: n in 3..6, delta in {1/2,...,19/20}, theta_h in [0, delta],
   chords drawn in the F window [theta+1, delta+1) and/or the
   L window (n+delta-1, n+delta-1+theta]; the defect must be 2 for
   one-sided stars and 3 for mixed stars.
Local gap/arc model only -- not geometric realizability.
"""
from fractions import Fraction as F
import random
from math import floor


def defect(n, gaps):
    cells = sum(floor(g) for g in gaps)
    big = sum(1 for g in gaps if g >= 1)
    assert cells <= n
    return big + n - cells


def row_gaps(theta, pi, chords):
    xs = sorted(chords)
    pts = [theta] + xs
    return [b - a for a, b in zip(pts, pts[1:])] + [theta + pi - xs[-1]]


def main():
    g = [F(11, 10), F(1, 10), F(47, 20), F(6, 5)]
    assert sum(g) == 4 + F(3, 4)
    assert [floor(x) for x in g] == [1, 0, 2, 1]
    assert defect(4, g) == 3
    print("packet c=3 example: OK (floors 1,0,2,1; c=3)")

    rng = random.Random(0)
    cnt = {2: 0, 3: 0}
    for n in range(3, 7):
        for dnum in range(10, 20):
            d = F(dnum, 20)
            pi = n + d
            for _ in range(200):
                th = F(rng.randint(0, 1000), 1000) * d
                def fch():
                    lo, hi = th + 1, d + 1
                    return lo + (hi - lo) * F(rng.randint(0, 999), 1000)
                def lch():
                    lo, hi = pi - 1, pi - 1 + th
                    if hi == lo:
                        return None
                    return hi - (hi - lo) * F(rng.randint(0, 999), 1000)
                k = rng.randint(1, 4)
                mode = rng.choice(["F", "L", "M"])
                chords = []
                for i in range(k):
                    side = mode if mode != "M" else ("F" if i % 2 == 0 else "L")
                    x = fch() if side == "F" else lch()
                    if x is None:
                        break
                    chords.append(x)
                else:
                    hasF = any(x < d + 1 for x in chords)
                    hasL = any(x > pi - 1 for x in chords)
                    want = 3 if (hasF and hasL) else 2
                    got = defect(n, row_gaps(th, pi, chords))
                    assert got == want, (n, d, th, chords, got, want)
                    cnt[want] += 1
    print("grid regression OK:", cnt)


if __name__ == "__main__":
    main()
