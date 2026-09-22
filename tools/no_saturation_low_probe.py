"""LOW deletion terminals and their hull profiles; discovery evidence only."""

from collections import Counter
from itertools import permutations, product
import json
import math
import random


def cross(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])


def hull(points):
    points = sorted(points)
    lower, upper = [], []
    for seq, acc in [(points, lower), (list(reversed(points)), upper)]:
        for p in seq:
            while len(acc) > 1 and cross(acc[-2], acc[-1], p) <= 0:
                acc.pop()
            acc.append(p)
    return lower[:-1]+upper[:-1]


def maximum_angle(points):
    return max(math.atan2(abs(cross(b, a, c)),
                         (a[0]-b[0])*(c[0]-b[0])+(a[1]-b[1])*(c[1]-b[1]))
               for a, b, c in permutations(points, 3))


def row_profile(points, lam):
    ks = []
    for i, p in enumerate(points):
        ds = sorted(math.atan2(q[1]-p[1], q[0]-p[0]) % math.pi
                    for j, q in enumerate(points) if i != j)
        gaps = [b-a for a, b in zip(ds, ds[1:]+[ds[0]+math.pi])]
        ks.append(sum(max(0, math.floor(g/lam+1e-10)-1) for g in gaps))
    return ks, sum(2**k for k in ks)


def analyze(points, n, delta):
    lam = math.pi/(n+delta)
    maximum = maximum_angle(points)
    if maximum > math.pi-lam+1e-9:
        return None
    ks, weight = row_profile(points, lam)
    if n-1 in ks:
        return None
    after = [row_profile(points[:i]+points[i+1:], lam)[1] for i in range(len(points))]
    boundary = hull(points)
    return {'n': n, 'delta': delta, 'points': points, 'exponents': ks,
            'potential': weight, 'cap': 2**n, 'deletion_potentials': after,
            'irreducible': max(after) < weight, 'hull_count': len(boundary),
            'interior_count': len(points)-len(boundary),
            'maximum_angle_degrees': math.degrees(maximum),
            'angle_cap_degrees': math.degrees(math.pi-lam)}


def binary_cluster(n):
    dirs = [(j+.2)*math.pi/n for j in range(n)]
    return [tuple(sum(bit*.01**j*(math.cos, math.sin)[z](dirs[j])
                      for j, bit in enumerate(bits)) for z in [0, 1])
            for bits in product([0, 1], repeat=n)]


def experiments():
    cases = {
        'minimal_tight_square': analyze([(-1., -1.), (1., -1.), (1., 1.), (-1., 1.)],
                                        2, .25),
        'minimal_nonflat_triangle_center': analyze(
            [(1., 0.), (-.5, math.sqrt(3)/2), (-.5, -math.sqrt(3)/2), (0., 0.)],
            3, 3/11),
        'integer_pentagon': analyze([(11, 6), (6, 10), (-5, 5), (-3, -7), (3, -9)],
                                   3, 3/7),
    }
    for n in range(2, 7):
        polygon = [(math.cos(j*math.pi/n), math.sin(j*math.pi/n)) for j in range(2*n)]
        cases[f'regular_{2*n}_gon'] = analyze(polygon, n, .25)
        cases[f'binary_cluster_n{n}'] = analyze(binary_cluster(n), n, .25)
    rng = random.Random(20260924)
    counts = Counter()
    terminals = {}
    for trial in range(12000):
        n, delta = rng.randrange(2, 7), rng.choice([.1, .25, .49])
        size = rng.randrange(4, 2*n+1)
        kind = ['circle', 'convex', 'interior'][trial % 3]
        points = []
        for j in range(size):
            theta = 2*math.pi*j/size+rng.uniform(-.3, .3)*2*math.pi/size
            radius = 1. if kind == 'circle' else rng.uniform(.5, 1.5)
            points.append((radius*math.cos(theta), radius*math.sin(theta)))
        if kind == 'convex':
            points = hull(points)
        elif kind == 'interior':
            points = hull(points)
            points.append((rng.uniform(-.15, .15), rng.uniform(-.15, .15)))
        if len(points) < 4:
            continue
        case = analyze(points, n, delta)
        if case is None:
            continue
        key = f'{kind}/n{n}'
        counts[key+'/legal_no_saturation'] += 1
        if case['irreducible']:
            counts[key+'/irreducible'] += 1
            if max(case['exponents']) > 0:
                counts[key+'/nonflat_irreducible'] += 1
            profile = (n, case['hull_count'], case['interior_count'],
                       tuple(sorted(case['exponents'], reverse=True)))
            terminals.setdefault(str(profile), case)
    return {'status': 'floating-point discovery evidence, not Lean proof',
            'named_cases': cases, 'sample_counts': dict(sorted(counts.items())),
            'representative_terminal_profiles': terminals}


if __name__ == '__main__':
    result = experiments()
    assert result['named_cases']['minimal_tight_square']['deletion_potentials'] == [3]*4
    assert result['named_cases']['minimal_nonflat_triangle_center']['deletion_potentials'] == [6]*4
    print(json.dumps(result, indent=2))
