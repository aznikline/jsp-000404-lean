#!/usr/bin/env python3
"""Floating-point corroboration of the exact obstruction in AVERAGED_BIN_PACKING.md."""
import itertools
import json
import math
import random


def direction(t):
    return (math.cos(t), math.sin(t))


def angle(p, q, r):
    u, v = (p[0]-q[0], p[1]-q[1]), (r[0]-q[0], r[1]-q[1])
    return math.atan2(abs(u[0]*v[1]-u[1]*v[0]), u[0]*v[0]+u[1]*v[1])


def row(points, i):
    return sorted(math.atan2(q[1]-points[i][1], q[0]-points[i][0]) % math.pi
                  for j, q in enumerate(points) if j != i)


def score(ds, lam):
    gaps = [b-a for a,b in zip(ds, ds[1:])] + [math.pi+ds[0]-ds[-1]]
    return sum(max(0, math.floor(g/lam+1e-10)-1) for g in gaps)


def case(n, rng, samples=1000):
    lam = math.pi/(n+0.75)
    theta, alpha, psi, gamma = (v*lam for v in (0.7,1.25,2.3,1.125))
    d = math.sin(theta)/math.sin(alpha)
    q = math.sin(alpha-theta)/math.sin(alpha)
    u = d*math.sin(psi-alpha)/math.sin(psi-gamma)
    points = [(0.,0.), direction(theta), (q,0.),
              (q+u*math.cos(gamma), u*math.sin(gamma))]
    max_angle = max(angle(points[i],points[j],points[k])
                    for i,j,k in itertools.permutations(range(4),3))
    assert max_angle < math.pi-lam
    scores = [score(row(points,i),lam) for i in range(4)]
    assert scores[0] == n-1 and scores[1] == scores[2] == n-2 and scores[3] <= n-2
    sums, ratios = set(), set()
    for _ in range(samples):
        # The corridor length is (n-1/2)*lambda. Every positive deficit
        # vector of sum lambda/2 produces n widths strictly below lambda.
        weights = [rng.expovariate(1) for _ in range(n)]
        widths = [lam-0.5*lam*w/sum(weights) for w in weights]
        ends, end = [], lam
        for width in widths:
            end += width
            ends.append(end)
        cubes = []
        for i in (1,2,3):
            phis = [math.atan2(points[j][1]-points[i][1], points[j][0]-points[i][0]) % math.pi
                    for j in (1,2,3) if j != i]
            bins = {min(next((b for b,r in enumerate(ends) if p < r), n-1), n-1) for p in phis}
            cubes.append(2**(n-len(bins)))
        assert cubes == [2**(n-2),2**(n-1),2**(n-2)]
        ratios.add(cubes[0]/2**scores[1])
        sums.add(sum(cubes))
    return {"n":n,"lambda":lam,"points_O_P_Q_R":points,"scores":scores,
            "max_angle":max_angle,"angle_cap":math.pi-lam,
            "partitions":samples,"P_cube_to_weight_ratios":sorted(ratios),
            "cube_totals":sorted(sums)}


if __name__ == "__main__":
    rng = random.Random(404)
    print(json.dumps([case(n,rng) for n in (3,4,5,8,12,20)],indent=2))
