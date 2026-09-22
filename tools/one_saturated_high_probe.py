"""Check concrete obstructions to an anchored HIGH cube-hole argument.

Integer assertions certify the rational four-center example's legality and
row exponents. The seven-center construction and angular bin membership use
floating-point discovery arithmetic. This script is not a Lean proof.
"""

from functools import cmp_to_key
from itertools import combinations, permutations, product
import json
import math
import random


def cross(u, v):
    return u[0]*v[1]-u[1]*v[0]


def dot(u, v):
    return u[0]*v[0]+u[1]*v[1]


def sub(p, q):
    return p[0]-q[0], p[1]-q[1]


def exact_four_certificate(points):
    """lambda=67.5 degrees: angle cap112.5; score threshold135."""
    legality_margins = []
    for p, q, r in permutations(points, 3):
        u, v = sub(p, q), sub(r, q)
        determinant, scalar = abs(cross(u, v)), dot(u, v)
        if scalar < 0:
            # tan(pi-angle)>1+sqrt(2), so angle<112.5 degrees.
            assert determinant+scalar > 0
            margin = (determinant+scalar)**2-2*scalar**2
            assert margin > 0
            legality_margins.append(margin)
    big_gaps = []
    for i, p in enumerate(points):
        vectors = []
        for j, q in enumerate(points):
            if i == j:
                continue
            u = sub(q, p)
            if u[1] < 0 or (u[1] == 0 and u[0] < 0):
                u = -u[0], -u[1]
            vectors.append(u)
        vectors.sort(key=cmp_to_key(lambda u, v: -cross(u, v)))
        large = 0
        for j, u in enumerate(vectors):
            v = vectors[(j+1) % len(vectors)]
            if j+1 == len(vectors):
                v = -v[0], -v[1]
            d, q = cross(u, v), dot(u, v)
            assert d > 0
            # A gap >=135 degrees contributes exactly1; every smaller gap0.
            large += int(q < 0 and d <= -q)
        big_gaps.append(large)
    assert big_gaps == [1, 0, 0, 0]
    return {'all_angles_strictly_below_112_5_degrees': True,
            'minimum_integer_legality_margin': min(legality_margins),
            'exact_row_exponents': big_gaps}


def analyze(points, n, delta):
    lam = math.pi/(n+delta)
    beta = math.pi-n*lam
    width = (math.pi-2*lam+beta)/n
    anchor = points[0]
    turn = min(math.atan2(p[1]-anchor[1], p[0]-anchor[0]) for p in points[1:])
    exponents = []
    maximum = 0
    for p, q, r in permutations(points, 3):
        u, v = sub(p, q), sub(r, q)
        maximum = max(maximum, math.atan2(abs(cross(u, v)), dot(u, v)))
    assert maximum < math.pi-lam
    for i, p in enumerate(points):
        ds = sorted(math.atan2(q[1]-p[1], q[0]-p[0]) % math.pi
                    for j, q in enumerate(points) if i != j)
        gaps = [b-a for a, b in zip(ds, ds[1:]+[ds[0]+math.pi])]
        exponents.append(sum(max(0, math.floor(g/lam)-1) for g in gaps))
    assert exponents[0] == n-1
    assert exponents.count(n-1) == 1
    bits = [[None]*n for _ in points[1:]]
    margin_slacks = []
    for i, j in combinations(range(len(points)-1), 2):
        u = sub(points[j+1], points[i+1])
        phase = (math.atan2(u[1], u[0])-turn) % (2*math.pi)
        line = phase % math.pi
        assert lam-1e-9 <= line <= math.pi-lam+beta+1e-9
        b = min(n-1, math.floor((line-lam)/width))
        positive = int(phase < math.pi)
        for v, bit in [(i, positive), (j, 1-positive)]:
            assert bits[v][b] in (None, bit)
            bits[v][b] = bit
            theta = math.atan2(points[v+1][1]-anchor[1], points[v+1][0]-anchor[0])-turn
            assert -1e-9 <= theta <= beta+1e-9
            slack = line-theta-lam if bit else theta+math.pi-lam-line
            assert slack >= -1e-9
            margin_slacks.append(slack)
    cubes = []
    for row, k in zip(bits, exponents[1:]):
        cube = {word for word in range(2**n)
                if all(b is None or (word >> j) & 1 == b for j, b in enumerate(row))}
        assert len(cube) >= 2**k
        assert all(cube.isdisjoint(other) for other in cubes)
        cubes.append(cube)
    candidates = []
    for coord in combinations(range(n), 2):
        for pattern in product([0, 1], repeat=2):
            corner = {word for word in range(2**n)
                      if all((word >> j) & 1 == b for j, b in zip(coord, pattern))}
            enough = all(len(cube-corner) >= 2**k
                         for cube, k in zip(cubes, exponents[1:]))
            if enough:
                candidates.append({'coordinates': coord, 'pattern': pattern})
    union = set().union(*cubes)
    actual = sum(2**k for k in exponents[1:])
    encoded = sum(map(len, cubes))
    return {'points': points, 'n': n, 'delta': delta,
            'lambda_degrees': math.degrees(lam), 'beta_degrees': math.degrees(beta),
            'bin_width_degrees': math.degrees(width),
            'minimum_per_vertex_forbidden_margin_slack_degrees':
                math.degrees(min(margin_slacks)),
            'maximum_angle_degrees': math.degrees(maximum),
            'angle_cap_degrees': math.degrees(math.pi-lam),
            'exponents': exponents,
            'rest_bit_patterns': [''.join('*' if b is None else str(b) for b in row)
                                  for row in bits],
            'actual_rest_weight': actual, 'target_rest_weight': 3*2**(n-2),
            'encoded_rest_weight': encoded, 'cube_size': 2**n,
            'unoccupied_words': 2**n-len(union), 'exponent_slack': encoded-actual,
            'possible_quarter_faces_after_trimming': candidates}


def retained_left_cluster(n=3, scale=.001, ratio=.01):
    phi = math.pi/(2*n+1)
    points = [(-1., 0.)]
    for center, dim, offset in [((1., 0.), n-1, 2),
                                 ((0., math.tan(phi)), n-2, 3)]:
        for bits in product([0, 1], repeat=dim):
            points.append(tuple(center[z]+scale*sum(
                bit*ratio**j*(math.cos, math.sin)[z]((2*j+offset)*phi)
                for j, bit in enumerate(bits)) for z in [0, 1]))
    return points


def integer_flexible_face_counterexample():
    points = [(-100000000, 0)]
    for center, offsets in [((100000000, 0), [(60000, 50000), (100, 600), (-3, 5)]),
                             ((0, 36000000), [(10000, 30100), (-100, 200)])]:
        for bits in product([0, 1], repeat=len(offsets)):
            points.append(tuple(center[z]+sum(bit*offsets[j][z]
                                for j, bit in enumerate(bits)) for z in [0, 1]))
    return points


def exact_flexible_face_certificate(points):
    """Certify the n=4 counterexample using only integer arithmetic.

    Set lambda=atan(3/4). All five uniform-bin boundary rays are rational.
    Exact signs of complex powers establish4<pi/lambda<5 and delta>1/2;
    the note supplies the elementary quadrant argument.
    """
    def complex_power(z, power):
        ans = (1, 0)
        for _ in range(power):
            ans = ans[0]*z[0]-ans[1]*z[1], ans[0]*z[1]+ans[1]*z[0]
        return ans

    assert complex_power((4, 3), 5) == (-3116, -237)
    assert complex_power((4, 3), 9) == (1721764, -922077)
    triangle_margins = []
    for p, q, r in permutations(points, 3):
        u, v = sub(p, q), sub(r, q)
        determinant, scalar = abs(cross(u, v)), dot(u, v)
        if scalar < 0:
            margin = 4*determinant+3*scalar
            assert margin > 0
            triangle_margins.append(margin)
    # beta=pi-4lambda has ray(527,336); all anchor rays are in[0,beta).
    for p in points[1:]:
        x, y = sub(p, points[0])
        assert x > 0 and y >= 0 and 527*y < 336*x
    # Every other row gap is strictly below2lambda, whose tangent is24/7.
    row_margins = []
    for i, p in enumerate(points[1:], 1):
        vectors = []
        for j, q in enumerate(points):
            if i == j:
                continue
            u = sub(q, p)
            if u[1] < 0 or (u[1] == 0 and u[0] < 0):
                u = -u[0], -u[1]
            vectors.append(u)
        vectors.sort(key=cmp_to_key(lambda u, v: -cross(u, v)))
        for j, u in enumerate(vectors):
            v = vectors[(j+1) % len(vectors)]
            if j+1 == len(vectors):
                v = -v[0], -v[1]
            determinant, scalar = cross(u, v), dot(u, v)
            margin = 24*scalar-7*determinant
            assert determinant >= 0 and scalar > 0 and margin > 0
            row_margins.append(margin)
    boundaries = [(4, 3), (1, 3), (-7, 24), (-307, 249), (-3116, 237)]
    assert all(cross(a, b) > 0 for a, b in combinations(boundaries, 2))
    bits = [[None]*4 for _ in points[1:]]
    for i, j in combinations(range(len(points)-1), 2):
        u = sub(points[j+1], points[i+1])
        positive = int(u[1] > 0)
        if not positive:
            u = -u[0], -u[1]
        bins = [b for b in range(4)
                if cross(boundaries[b], u) > 0 and cross(u, boundaries[b+1]) > 0]
        assert len(bins) == 1
        for vertex, bit in [(i, positive), (j, 1-positive)]:
            assert bits[vertex][bins[0]] in (None, bit)
            bits[vertex][bins[0]] = bit
    words = [''.join('*' if b is None else str(b) for b in row) for row in bits]
    expected = ['1111', '1101', '1011', '1001', '0111', '0101', '0011', '0001',
                '*110', '1100', '0010', '*000']
    assert words == expected
    # These fixed cubes alone meet every codimension2 face of the4-cube.
    fixed = [row for row in bits if None not in row]
    assert all(any(all(row[j] == b for j, b in zip(coord, pattern)) for row in fixed)
               for coord in combinations(range(4), 2) for pattern in product([0, 1], repeat=2))
    return {'lambda': 'atan(3/4)', 'strip_index': 4, 'high_regime': True,
            'complex_fifth_power': [-3116, -237], 'complex_ninth_power': [1721764, -922077],
            'minimum_integer_angle_margin': min(triangle_margins),
            'minimum_integer_nonanchor_gap_margin': min(row_margins),
            'exact_bin_boundary_rays': boundaries, 'exact_bin_words': words,
            'all_24_quarter_faces_meet_a_fixed_weight_one_cube': True,
            'exact_row_exponents': [3]+[0]*12}


def standard_cluster_sweep():
    results = []
    for n in range(3, 7):
        for delta in [.55, .65, .75, .85, .95]:
            for ratio in [.002, .01, .03]:
                points = retained_left_cluster(n, ratio=ratio)
                cap = math.pi-math.pi/(n+delta)
                maximum = max(math.atan2(abs(cross(sub(p, q), sub(r, q))),
                                         dot(sub(p, q), sub(r, q)))
                              for p, q, r in permutations(points, 3))
                row = {'n': n, 'delta': delta, 'ratio': ratio, 'legal': maximum < cap}
                if maximum < cap:
                    case = analyze(points, n, delta)
                    row.update({'face_count': len(case['possible_quarter_faces_after_trimming']),
                                'actual_rest_weight': case['actual_rest_weight'],
                                'target_rest_weight': case['target_rest_weight'],
                                'angle_margin_degrees': math.degrees(cap-maximum)})
                results.append(row)
    return results


if __name__ == '__main__':
    rational = [(-1000, 0), (1000, 0), (1001, 3), (0, 700)]
    four = analyze(rational, 2, 2/3)
    four['exact_integer_certificate'] = exact_four_certificate(rational)
    seven = analyze(retained_left_cluster(), 3, .75)
    exact_counter_points = integer_flexible_face_counterexample()
    flexible_counter = analyze(exact_counter_points, 4, math.pi/math.atan2(3, 4)-4)
    flexible_counter['exact_integer_certificate'] = exact_flexible_face_certificate(exact_counter_points)
    assert flexible_counter['possible_quarter_faces_after_trimming'] == []
    sweep = standard_cluster_sweep()
    assert four['unoccupied_words'] == seven['unoccupied_words'] == 0
    assert four['actual_rest_weight'] == four['target_rest_weight']
    assert seven['actual_rest_weight'] == seven['target_rest_weight']
    assert all(c['coordinates'] != (0, 2)
               for c in seven['possible_quarter_faces_after_trimming'])
    print(json.dumps({'status': 'exact integer checks where labeled; otherwise floating-point '
                      'discovery evidence; no Lean proof',
                      'four_center': four, 'seven_center': seven,
                      'any_coordinate_face_counterexample': flexible_counter,
                      'standard_retained_left_cluster_sweep': sweep}, indent=2))
