"""Probe the single-cut directional subcube mechanism (not a proof).

Only standard-library arithmetic is used. Every graph-changing angular cut is
tested by a midpoint between consecutive events. The omitted interval has
length pi - n*lambda; the other n intervals have width lambda.
"""

from itertools import combinations, permutations
from functools import cmp_to_key
import json
import math
from pathlib import Path


def row_exponents(points, lam):
    ans = []
    for i, p in enumerate(points):
        ds = sorted(math.atan2(q[1]-p[1], q[0]-p[0]) % math.pi
                    for j, q in enumerate(points) if i != j)
        gaps = [b-a for a, b in zip(ds, ds[1:]+[ds[0]+math.pi])]
        ans.append(sum(max(0, math.floor(g/lam+1e-10)-1) for g in gaps))
    return ans


def maximum_angle(points):
    def angle(p, q, r):
        x, y = (p[0]-q[0], p[1]-q[1]), (r[0]-q[0], r[1]-q[1])
        return math.atan2(abs(x[0]*y[1]-x[1]*y[0]), x[0]*y[0]+x[1]*y[1])
    return max(angle(*triple) for triple in permutations(points, 3))


def exact_integer_certificate(points):
    """Exact checks imply all angles <=120 degrees and all global gaps <22.5.

    For a negative dot product q, 4*q*q <= |u|^2*|v|^2 implies
    cos(angle)>=-1/2. For a positive adjacent determinant d and dot q,
    (q+d)^2 < 2*q*q implies tan(gap)<sqrt(2)-1.
    The implications use elementary Euclidean geometry; this is not Lean.
    """
    for p, q, r in permutations(points, 3):
        u = p[0]-q[0], p[1]-q[1]
        v = r[0]-q[0], r[1]-q[1]
        dot = u[0]*v[0]+u[1]*v[1]
        assert dot >= 0 or 4*dot*dot <= sum(x*x for x in u)*sum(x*x for x in v)
    vecs = []
    for i, j in combinations(range(len(points)), 2):
        x, y = points[j][0]-points[i][0], points[j][1]-points[i][1]
        if y < 0 or (y == 0 and x < 0):
            x, y = -x, -y
        vecs.append(((x, y), (i, j)))
    vecs.sort(key=cmp_to_key(lambda a, b: -(a[0][0]*b[0][1]-a[0][1]*b[0][0])))
    for a, b in combinations(vecs, 2):
        assert a[0][0]*b[0][1]-a[0][1]*b[0][0] > 0
    for vertex in range(len(points)):
        row = [v for v, pair in vecs if vertex in pair]
        for i, (x, y) in enumerate(row):
            u, v = row[(i+1) % len(row)]
            if i+1 == len(row):
                u, v = -u, -v
            assert x*v-y*u > 0 and x*u+y*v > 0
    cert = []
    for i, ((x, y), pair) in enumerate(vecs):
        (u, v), _ = vecs[(i+1) % len(vecs)]
        if i+1 == len(vecs):
            u, v = -u, -v
        det, dot = x*v-y*u, x*u+y*v
        margin = 2*dot*dot-(dot+det)**2
        assert det > 0 and dot > 0 and margin > 0
        cert.append({'edge': pair, 'vector': (x, y), 'determinant': det,
                     'dot_product': dot, 'strict_integer_margin': margin})
    return {'all_angles_le_120_degrees': True,
            'all_projective_gaps_lt_22_5_degrees': True,
            'all_individual_row_gaps_lt_90_degrees': True,
            'adjacent_direction_certificates': cert}


def analyze_cut(points, n, lam, cut, exponents):
    bits = [[None]*(n+1) for _ in points]
    for i, j in combinations(range(len(points)), 2):
        phase = (math.atan2(points[j][1]-points[i][1],
                            points[j][0]-points[i][0])-cut) % (2*math.pi)
        idx = min(n, math.floor((phase % math.pi)/lam))
        positive = phase < math.pi
        for v, bit in [(i, int(positive)), (j, int(not positive))]:
            assert bits[v][idx] in (None, bit), (v, idx, cut)
            bits[v][idx] = bit
    cubes = []
    deficits = 0
    surpluses = 0
    for k, row in zip(exponents, bits):
        empty = sum(b is None for b in row[:n])
        assert k <= empty + (row[n] is None)
        cube = {word for word in range(2**n)
                if all(b is None or (word >> i) & 1 == b
                       for i, b in enumerate(row[:n]))}
        assert len(cube) == 2**empty
        if k > empty:
            assert row[n] is None and k == empty+1
            deficits += len(cube)
        else:
            surpluses += len(cube) - 2**k
        cubes.append(cube)
    multiplicities = [sum(word in cube for cube in cubes) for word in range(2**n)]
    assert max(multiplicities) <= 2
    overlaps = sum(m == 2 for m in multiplicities)
    unused = sum(m == 0 for m in multiplicities)
    assert sum(2**k for k in exponents) == 2**n-unused+overlaps+deficits-surpluses
    return {"cut_degrees": math.degrees(cut), "overlap": overlaps,
            "deficit": deficits, "surplus": surpluses, "unused": unused,
            "coarse_excess": overlaps+deficits,
            "bits": [''.join('*' if b is None else str(b) for b in row)
                     for row in bits]}


def analyze(points, n, delta):
    lam = math.pi/(n+delta)
    ds = sorted(set(math.atan2(q[1]-p[1], q[0]-p[0]) % math.pi
                    for p, q in combinations(points, 2)))
    gaps = [b-a for a, b in zip(ds, ds[1:]+[ds[0]+math.pi])]
    events = sorted(set(round((d-j*lam) % math.pi, 12)
                        for d in ds for j in range(n+1)))
    cuts = [((a+b)/2) % math.pi
            for a, b in zip(events, events[1:]+[events[0]+math.pi])]
    ks = row_exponents(points, lam)
    results = [analyze_cut(points, n, lam, cut, ks) for cut in cuts]
    return {"points": points, "n": n, "delta": delta,
            "lambda_degrees": math.degrees(lam),
            "angle_cap_degrees": math.degrees(math.pi-lam),
            "maximum_angle_degrees": math.degrees(maximum_angle(points)),
            "global_directions_degrees": list(map(math.degrees, ds)),
            "max_global_gap_degrees": math.degrees(max(gaps)),
            "omitted_width_degrees": math.degrees(math.pi-n*lam),
            "exponents": ks, "potential": sum(2**k for k in ks),
            "tested_cut_intervals": len(cuts),
            "minimum_coarse_excess": min(r['coarse_excess'] for r in results),
            "maximum_coarse_excess": max(r['coarse_excess'] for r in results),
            "best_cut": min(results, key=lambda r: r['coarse_excess']),
            "worst_cut": max(results, key=lambda r: r['coarse_excess'])}


if __name__ == '__main__':
    source = Path(__file__).resolve().parent.parent / 'verification/no-saturation-geometry.json'
    existing = json.loads(source.read_text())['cases']
    cases = {
        'integer_pentagon_low': analyze([(11, 6), (6, 10), (-5, 5), (-3, -7), (3, -9)],
                                       3, 3/7),
        'regular_pentagon_high': analyze(existing['regular_pentagon']['points'], 2, .75),
        'nonflat_nine_high': analyze(existing['nonflat_nine_point_cluster']['points'], 3, .75),
    }
    cases['integer_pentagon_low']['exact_integer_certificate'] = exact_integer_certificate(
        cases['integer_pentagon_low']['points'])
    print(json.dumps({'status': 'floating-point discovery evidence, not a Lean theorem',
                      'cases': cases}, indent=2))
