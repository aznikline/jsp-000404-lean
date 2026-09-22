#!/usr/bin/env python3
"""Reproducible floating-point checks of the proposed two-anchor corridor.

This is a falsification probe, not a proof. Near-integer quotients are snapped
within 1e-10 solely to make named exact-grid fixtures stable in binary floats.
"""

import json
import math
import random

PI = math.pi
TOL = 2e-9
A = (0.0, 0.0)
B = (1.0, 0.0)


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def angle(p, q, r):
    u, v = sub(p, q), sub(r, q)
    return math.atan2(abs(u[0] * v[1] - u[1] * v[0]),
                      u[0] * v[0] + u[1] * v[1])


def line_rep(p, q):
    u = sub(q, p)
    return math.atan2(u[1], u[0]) % PI


def floor_stable(x):
    nearest = round(x)
    return nearest if abs(x - nearest) < 1e-10 else math.floor(x)


def gap_score(lam, gap):
    return max(0, max(0, floor_stable(gap / lam)) - 1)


def row(points, i):
    return sorted(line_rep(points[i], p) for j, p in enumerate(points) if j != i)


def row_score(points, i, lam):
    ds = row(points, i)
    gaps = [y - x for x, y in zip(ds, ds[1:])]
    return sum(gap_score(lam, g) for g in gaps + [PI + ds[0] - ds[-1]])


def point_from_angles(a, b):
    ta, tb = math.tan(a), math.tan(b)
    return (tb / (ta + tb), ta * tb / (ta + tb))


def legal(points, lam):
    return all(angle(points[i], points[j], points[k]) <= PI - lam + TOL
               for j in range(len(points))
               for i in range(len(points)) if i != j
               for k in range(i + 1, len(points)) if k != j)


def inspect(points, n, lam):
    beta = PI - n * lam
    aa = [angle(B, A, p) for p in points[2:]]
    bb = [angle(A, B, p) for p in points[2:]]
    ia, ib = min(range(len(aa)), key=aa.__getitem__), min(range(len(bb)), key=bb.__getitem__)
    assert ia == ib, ("incompatible minima", aa, bb)
    a0, b0 = aa[ia], bb[ib]
    assert max(aa + bb) <= beta + TOL
    assert a0 + b0 >= lam - TOL
    left, right = lam + a0, PI - lam - b0
    m = n - 2
    width = (right - left) / m
    assert 0 < width < lam + TOL
    assert row_score(points, 0, lam) == n - 1
    assert row_score(points, 1, lam) == n - 1
    occupied = []
    max_identity_error = 0.0
    min_corridor_slack = math.inf
    for i in range(2, len(points)):
        full = row(points, i)
        middle = sorted(line_rep(points[i], points[j])
                        for j in range(2, len(points)) if j != i)
        expected = [aa[i-2]] + middle + [PI - bb[i-2]]
        assert len(full) == len(expected)
        assert max(abs(x-y) for x, y in zip(full, expected)) < TOL
        assert aa[i-2] + bb[i-2] < 2 * lam
        assert gap_score(lam, aa[i-2] + bb[i-2]) == 0
        assert left - aa[i-2] <= lam + TOL
        assert (PI - bb[i-2]) - right <= lam + TOL
        for phi in middle:
            assert left - TOL <= phi <= right + TOL
            min_corridor_slack = min(min_corridor_slack, phi-left, right-phi)
        bins = {min(m-1, max(0, floor_stable((phi-left) / width))) for phi in middle}
        occupied.append(len(bins))
        assert row_score(points, i, lam) <= m - len(bins)
    for i in range(2, len(points)):
        for j in range(i+1, len(points)):
            # Samples are generated in the common increasing angular order.
            C, D = points[i], points[j]
            phi = math.atan2(D[1]-C[1], D[0]-C[0])
            assert 0 < phi < PI
            assert lam + aa[i-2] - TOL <= phi <= PI - lam - bb[i-2] + TOL
            errors = [abs(angle(A, C, D) - (PI + aa[i-2] - phi)),
                      abs(angle(B, C, D) - (bb[i-2] + phi))]
            max_identity_error = max(max_identity_error, *errors)
            t = C[1] / (D[1] - C[1])
            ex = C[0] + t * (C[0] - D[0])
            assert -TOL < ex < 1 + TOL
    rest_weight = sum(2 ** row_score(points, i, lam) for i in range(2, len(points)))
    cube_weight = sum(2 ** (m - k) for k in occupied)
    assert rest_weight <= cube_weight <= 2 ** m
    return max_identity_error, min_corridor_slack, rest_weight, cube_weight


def run(seed=404, attempts_per_case=5000):
    rng = random.Random(seed)
    accepted = {}
    accepted_by_mode = {"nested_angular_samples": 0, "unconstrained_pairing": 0}
    attempted = 0
    max_error = 0.0
    min_slack = math.inf
    first_example = None
    for n in range(3, 10):
        for rest in range(2, 6):
            count = 0
            for attempt in range(attempts_per_case):
                attempted += 1
                delta = rng.uniform(0.505, 0.995)
                lam = PI / (n + delta)
                beta = delta * lam
                lower = lam - beta
                aa = sorted(rng.uniform(lower, beta) for _ in range(rest))
                bb = [rng.uniform(lower, beta) for _ in range(rest)]
                mode = "nested_angular_samples" if attempt % 2 == 0 else "unconstrained_pairing"
                if mode == "nested_angular_samples":
                    bb.sort()
                if any(a + b < lam for a, b in zip(aa, bb)):
                    continue
                points = [A, B] + [point_from_angles(a, b) for a, b in zip(aa, bb)]
                if not legal(points, lam):
                    continue
                error, slack, _, _ = inspect(points, n, lam)
                max_error, min_slack = max(max_error, error), min(min_slack, slack)
                count += 1
                accepted_by_mode[mode] += 1
                if first_example is None:
                    first_example = (points, n, lam)
            accepted[f"n={n},centers={rest+2}"] = count

    # Place the sole non-anchor chord exactly at the common left endpoint,
    # interior bin boundary, or right endpoint, with n=4 and two bins.
    fixtures = []
    n, lam = 4, PI / 4.8
    a, b = 0.55 * lam, 0.56 * lam
    C = point_from_angles(a, b)
    left, right = lam + a, PI - lam - b
    for name, phi in [("left", left), ("internal", (left+right)/2), ("right", right)]:
        D = (C[0] + 0.01 * math.cos(phi), C[1] + 0.01 * math.sin(phi))
        points = [A, B, C, D]
        assert legal(points, lam)
        error, slack, weight, cube = inspect(points, n, lam)
        max_error = max(max_error, error)
        fixtures.append({"boundary": name,
                         "bin": min(1, max(0, floor_stable((line_rep(C,D)-left)/((right-left)/2)))),
                         "corridor_slack": slack, "rest_weight": weight, "cube_weight": cube})

    points, n, lam = first_example
    reflected = [(p[0], -p[1]) for p in points]
    P = reflected[2]
    a, b = angle(B, A, P), angle(A, B, P)
    actual = (line_rep(P, A), line_rep(P, B))
    orientation = {
        "n": n, "lambda": lam,
        "a": a, "b": b,
        "reflected_anchor_reps_to_A_B": actual,
        "naive_positive_side_formula_to_A_B": (a, PI-b),
        "correct_negative_side_formula_to_A_B": (PI-a, b),
        "maximum_naive_error": max(abs(actual[0]-a), abs(actual[1]-(PI-b))),
        "swapping_anchor_labels_restores_formula":
            abs(actual[1]-b) < TOL and abs(actual[0]-(PI-a)) < TOL,
    }
    return {"seed": seed, "attempted": attempted,
            "accepted": sum(accepted.values()), "accepted_by_case": accepted,
            "accepted_by_mode": accepted_by_mode,
            "max_angle_identity_error": max_error,
            "minimum_random_corridor_slack": min_slack,
            "closed_endpoint_fixtures": fixtures,
            "orientation_counterexample": orientation}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
