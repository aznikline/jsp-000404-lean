"""Reproduce geometric counterexamples to the no-saturation K<=1 shortcut.

Floating-point discovery evidence only. The exact strict five-center
ModeA counterexample is checked separately in PentagonPacking.lean.
The three-cluster coordinates follow the attributed upper construction
in ThirdParty/Sendov/JSP404/ThreeClusterGeometry.lean.
"""
import itertools
import json
import math
from fractions import Fraction


def analyze(points, n, delta):
    lam = math.pi / (n + delta)
    ks, distances = [], []
    for i, p in enumerate(points):
        directions = sorted(
            math.atan2(q[1] - p[1], q[0] - p[0]) % math.pi
            for j, q in enumerate(points) if i != j
        )
        gaps = [b - a for a, b in zip(
            directions, directions[1:] + [directions[0] + math.pi])]
        ratios = [g / lam for g in gaps]
        ks.append(sum(max(math.floor(g) - 1, 0) for g in ratios))
        distances.extend(abs(g - round(g)) for g in ratios)
    angles = []
    for p, q, r in itertools.permutations(points, 3):
        x = p[0] - q[0], p[1] - q[1]
        y = r[0] - q[0], r[1] - q[1]
        angles.append(math.atan2(abs(x[0] * y[1] - x[1] * y[0]),
                                 x[0] * y[0] + x[1] * y[1]))
    maximum = max(angles)
    kraft = Fraction(sum(2 ** k for k in ks), 2 ** n)
    return {
        "n": n, "delta": delta, "points": points, "exponents": ks,
        "saturated_count": sum(k == n - 1 for k in ks),
        "kraft": str(kraft),
        "max_angle_degrees": math.degrees(maximum),
        "cap_angle_degrees": math.degrees(math.pi - lam),
        "legality_margin_degrees": math.degrees(math.pi - lam - maximum),
        "nearest_floor_boundary_distance": min(distances),
        "minimum_point_distance": min(math.dist(p, q)
            for p, q in itertools.combinations(points, 2)),
    }


def cluster_points(n=3, outer_scale=0.001, inner_scale=0.01):
    phi = math.pi / (2 * n + 1)
    centers = [(-1., 0.), (1., 0.), (0., math.tan(phi))]
    points = []
    for center, dim, offset in zip(centers, [n-1, n-1, n-2], [3, 2, 3]):
        for bits in itertools.product([0, 1], repeat=dim):
            points.append(tuple(center[z] + outer_scale * sum(
                bit * inner_scale ** j * (math.cos, math.sin)[z]((2*j+offset)*phi)
                for j, bit in enumerate(bits)) for z in (0, 1)))
    return points


if __name__ == "__main__":
    pentagon = [(math.cos(2*math.pi*j/5), math.sin(2*math.pi*j/5))
                for j in range(5)]
    ten = cluster_points()
    cases = {
        "regular_pentagon": analyze(pentagon, 2, 0.75),
        "ten_point_cluster": analyze(ten, 3, 0.75),
        "nonflat_nine_point_cluster": analyze(ten[1:], 3, 0.75),
    }
    for name, case in cases.items():
        assert case["saturated_count"] == 0, name
        assert case["kraft"] == "5/4", name
        assert case["legality_margin_degrees"] > 0.01, name
        assert case["nearest_floor_boundary_distance"] > 1e-9, name
        assert case["minimum_point_distance"] > 1e-8, name
    assert max(cases["nonflat_nine_point_cluster"]["exponents"]) > 0
    print(json.dumps({"status": "floating-point evidence; not a Lean proof",
                      "cases": cases}, indent=2))
