#!/usr/bin/env python3
"""Falsification probes for geometry-driven one-saturated HIGH splits.

The small integer fixture is certified with exact integer comparisons.
Adaptive interval-cover searches and random examples use floating-point
discovery arithmetic and are not proofs of universal statements.
"""

from functools import cmp_to_key, lru_cache
from itertools import combinations, permutations
import json
import math
import random

from one_saturated_high_probe import (
    cross, dot, sub, integer_flexible_face_counterexample, retained_left_cluster,
    exact_flexible_face_certificate,
)

PI = math.pi
TOL = 1e-9


def angle(p, q, r):
    u, v = sub(p, q), sub(r, q)
    return math.atan2(abs(cross(u, v)), dot(u, v))


def scores(points, lam):
    result = []
    for i, p in enumerate(points):
        row = sorted(math.atan2(q[1]-p[1], q[0]-p[0]) % PI
                     for j, q in enumerate(points) if i != j)
        gaps = [y-x for x, y in zip(row, row[1:]+[row[0]+PI])]
        result.append(sum(max(0, math.floor(g/lam+1e-10)-1) for g in gaps))
    return result


def exact_split_obstruction():
    points = [(0, 0), (10, 0), (7, 2), (9, 5)]
    powers = [(4, 3), (7, 24), (-44, 117), (-527, 336)]
    legal_margins = []
    for p, q, r in permutations(points, 3):
        u, v = sub(p, q), sub(r, q)
        d, scalar = abs(cross(u, v)), dot(u, v)
        assert d > 0
        if scalar < 0:
            assert 4*d+3*scalar > 0
            legal_margins.append(4*d+3*scalar)
    exponents = []
    floor_margins = []
    for i, p in enumerate(points):
        row = []
        for j, q in enumerate(points):
            if i == j:
                continue
            u = sub(q, p)
            if u[1] < 0 or (u[1] == 0 and u[0] < 0):
                u = (-u[0], -u[1])
            row.append(u)
        row.sort(key=cmp_to_key(lambda u, v: -cross(u, v)))
        k = 0
        for j, u in enumerate(row):
            v = row[(j+1) % len(row)]
            if j+1 == len(row):
                v = (-v[0], -v[1])
            d, scalar = cross(u, v), dot(u, v)
            assert d > 0
            margins = [x*d-y*scalar for x, y in powers]
            assert all(m != 0 for m in margins)
            floor_margins.extend(abs(m) for m in margins)
            floor = sum(m > 0 for m in margins)
            k += max(0, floor-1)
        exponents.append(k)
    assert exponents == [3, 1, 1, 1]
    narrow_margins = []
    for p, q in combinations(points[1:], 2):
        d, scalar = abs(cross(p, q)), dot(p, q)
        # alpha = 5*lambda-pi has the positive ray (3116,237).
        margin = 3116*d-237*scalar
        assert margin > 0
        narrow_margins.append(margin)
    bad_second_anchor = []
    for i in range(1, 4):
        margins = []
        for j in range(1, 4):
            if j == i:
                continue
            u, v = sub(points[0], points[i]), sub(points[j], points[i])
            d, scalar = abs(cross(u, v)), dot(u, v)
            margins.append(4*d-3*scalar)
        assert max(margins) > 0
        bad_second_anchor.append(max(margins))
    return dict(points=points, exponents=exponents,
                minimum_legality_integer_margin=min(legal_margins),
                minimum_floor_boundary_integer_margin=min(floor_margins),
                minimum_pairwise_alpha_separation_margin=min(narrow_margins),
                second_anchor_fan_over_lambda_integer_witnesses=bad_second_anchor)


def exact_thirteen_two_group_certificate():
    """Separate binary clusters use independent 3-bin and 2-bin covers."""
    points = integer_flexible_face_counterexample()
    exact_flexible_face_certificate(points)
    certificates = []
    for first, size, dim in [(1,8,3),(9,4,2)]:
        families = [[] for _ in range(dim)]
        active = [set() for _ in range(size)]
        for i,j in combinations(range(size),2):
            differing = (i^j).bit_length()-1
            family = dim-1-differing
            u = sub(points[first+j],points[first+i])
            assert u[1]>0
            families[family].append(u)
            active[i].add(family)
            active[j].add(family)
        margins = []
        for family in families:
            for u,v in combinations(family,2):
                scalar, determinant = dot(u,v),abs(cross(u,v))
                margin = 3*scalar-4*determinant
                assert scalar>0 and margin>0
                margins.append(margin)
        separation_margins = []
        for left,right in combinations(range(dim),2):
            for u in families[left]:
                for v in families[right]:
                    margin = cross(u,v)
                    assert margin>0
                    separation_margins.append(margin)
        assert all(len(a)==dim for a in active)
        certificates.append(dict(first_index=first,vertices=size,bins=dim,
            active_bins_per_vertex=dim,original_exponent_per_vertex=0,
            exact_weight=size,capacity=2**dim,
            minimum_integer_bin_width_margin=min(margins),
            minimum_integer_cross_family_separation=min(separation_margins)))
    return certificates


def group_cover(points, exponents, group, m, lam):
    """Search arbitrary contiguous angular bins, each strictly <lambda.

    Every row must use at most m-k_i active bins. Unused bins are allowed.
    This is a local sufficient certificate, not a total-weight comparison.
    """
    if any(exponents[i] > m for i in group):
        return None
    if len(group) <= 1:
        return dict(cut=0.0, bins=[])
    if m <= 0:
        return None
    local = {v: i for i, v in enumerate(group)}
    budgets = tuple(m-exponents[i] for i in group)
    edges = []
    for i, j in combinations(group, 2):
        u = sub(points[j], points[i])
        edges.append((math.atan2(u[1], u[0]) % PI, local[i], local[j]))
    edges.sort()
    for cut_index in range(len(edges)):
        if cut_index and edges[cut_index][0]-edges[cut_index-1][0] <= TOL:
            continue
        cut = edges[cut_index][0]
        ordered = edges[cut_index:]+[(a+PI, i, j) for a, i, j in edges[:cut_index]]
        # Avoid splitting equal direction classes across two bins.
        @lru_cache(None)
        def search(pos, used, counts):
            if pos == len(ordered):
                return ()
            if used == m:
                return None
            last = pos
            mask = set()
            candidates = []
            while last < len(ordered) and ordered[last][0]-ordered[pos][0] < lam-TOL:
                mask.update(ordered[last][1:])
                next_counts = tuple(x+int(v in mask) for v, x in enumerate(counts))
                if any(x > b for x, b in zip(next_counts, budgets)):
                    break
                if last+1 == len(ordered) or ordered[last+1][0]-ordered[last][0] > TOL:
                    candidates.append((last+1, next_counts))
                last += 1
            for end, next_counts in reversed(candidates):
                tail = search(end, used+1, next_counts)
                if tail is not None:
                    return ((ordered[pos][0]-cut, ordered[end-1][0]-cut),)+tail
            return None
        found = search(0, 0, (0,)*len(group))
        if found is not None:
            return dict(cut=cut, bins=found)
    return None


def prefix_split(points, n, lam):
    ks = scores(points, lam)
    anchor = points[0]
    order = sorted(range(1, len(points)), key=lambda i:
                   math.atan2(points[i][1]-anchor[1], points[i][0]-anchor[0]))
    cache = {}
    def cover(group, m):
        key = tuple(group), m
        if key not in cache:
            cache[key] = group_cover(points, ks, group, m, lam)
        return cache[key]
    for split in range(len(order)+1):
        left, right = order[:split], order[split:]
        for large, small in [(left, right), (right, left)]:
            first = cover(large, n-1)
            if first is None:
                continue
            second = cover(small, n-2)
            if second is not None:
                validate_cover(points,ks,large,n-1,lam,first)
                validate_cover(points,ks,small,n-2,lam,second)
                return dict(large=large, small=small, large_cover=first,
                            small_cover=second, exponents=ks)
    return None


def validate_cover(points, exponents, group, m, lam, certificate):
    """Independently recompute membership and local row inequalities."""
    bins = certificate['bins']
    assert len(bins)<=m
    assert all(0<=left<=right<PI and right-left<lam-TOL for left,right in bins)
    assert all(right<next_left-TOL for (_,right),(next_left,_) in zip(bins,bins[1:]))
    active = {i:set() for i in group}
    for i,j in combinations(group,2):
        u = sub(points[j],points[i])
        phi = (math.atan2(u[1],u[0])-certificate['cut']) % PI
        if abs(phi-PI)<TOL:
            phi=0.0
        members = [b for b,(left,right) in enumerate(bins) if left-TOL<=phi<=right+TOL]
        assert len(members)==1,(phi,bins)
        active[i].add(members[0])
        active[j].add(members[0])
    assert all(exponents[i]+len(active[i])<=m for i in group)


def run():
    rng = random.Random(404901)
    named = []
    for name, points, n, lam in [
        ('exact_four_split_obstruction', [(0,0),(10,0),(7,2),(9,5)], 4, math.atan2(3,4)),
        ('exact_thirteen_face_obstruction', integer_flexible_face_counterexample(), 4, math.atan2(3,4)),
        ('seven_cluster', retained_left_cluster(), 3, PI/3.75),
    ]:
        named.append(dict(name=name, certificate=prefix_split(points,n,lam)))
    tested = 0
    failures = []
    accepted = {}
    structured_tested = 0
    structured_sizes = {}
    for n in [3,4,5]:
        full = retained_left_cluster(n=n, ratio=.007)
        for _ in range(150):
            delta = rng.uniform(.55,.99)
            lam = PI/(n+delta)
            size = rng.randint(3,min(12,len(full)-1))
            selected = sorted(rng.sample(range(1,len(full)),size))
            points = [full[0]]+[full[i] for i in selected]
            maximum = max(angle(points[i],points[j],points[k])
                          for i,j,k in permutations(range(size+1),3))
            if maximum >= PI-lam-1e-8:
                continue
            ks = scores(points,lam)
            if ks[0] != n-1 or ks.count(n-1) != 1:
                continue
            structured_tested += 1
            key = f'n={n},rest={size}'
            structured_sizes[key] = structured_sizes.get(key,0)+1
            if prefix_split(points,n,lam) is None:
                failures.append(dict(kind='structured subset',n=n,delta=delta,
                    points=points,exponents=ks,maximum_angle=maximum,cap=PI-lam,
                    rest_weight=sum(2**k for k in ks[1:]),target=3*2**(n-2)))
                if len(failures)>=3:
                    break
        if len(failures)>=3:
            break
    for n in [2,3,4,5]:
        for rest in range(2, min(9, 2**n)):
            got = 0
            for _ in range(1500):
                delta = rng.uniform(.501,.999)
                lam = PI/(n+delta)
                beta = delta*lam
                width = rng.uniform(.02,1)*beta
                points = [(0.,0.)]
                for j in range(rest):
                    theta = rng.uniform(0,width)
                    radius = rng.uniform(.5,1.5)
                    points.append((radius*math.cos(theta),radius*math.sin(theta)))
                maximum = max(angle(points[i],points[j],points[k])
                              for i,j,k in permutations(range(rest+1),3))
                if maximum >= PI-lam-1e-8:
                    continue
                ks = scores(points,lam)
                if ks[0] != n-1 or ks.count(n-1) != 1:
                    continue
                got += 1
                tested += 1
                cert = prefix_split(points,n,lam)
                if cert is None:
                    failures.append(dict(n=n,delta=delta,points=points,exponents=ks,
                        maximum_angle=maximum,cap=PI-lam,
                        rest_weight=sum(2**k for k in ks[1:]),target=3*2**(n-2)))
                    if len(failures) >= 3:
                        break
            accepted[f'n={n},rest={rest}'] = got
            if len(failures)>=3:
                break
        if len(failures)>=3:
            break
    return dict(status='exact named integer checks; adaptive/random search is non-proof evidence',
                exact_obstruction=exact_split_obstruction(),
                exact_thirteen_two_group_certificate=exact_thirteen_two_group_certificate(),
                named=named,tested=tested,
                accepted=accepted,structured_tested=structured_tested,
                structured_sizes=structured_sizes,adaptive_angular_prefix_failures=failures)


if __name__ == '__main__':
    print(json.dumps(run(),indent=2))
