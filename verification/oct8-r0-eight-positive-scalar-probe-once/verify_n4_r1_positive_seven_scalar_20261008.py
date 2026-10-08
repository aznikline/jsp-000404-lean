#!/usr/bin/env python3
"""Exact GenericModel6 4 R1 verifier. No solver, no search, no Lean.

Input JSON: n=4, heavy=0 or5, rational delta, theta[6], d with exactly the
15 canonical keys i,j (i<j). Rational values are integer/string only, never
JSON floats. Optional word_bits[20], row_orders[6][5], and floors[6][6]
are compared to independently recomputed data. This verifies necessary
scalar data, NOT planar realizability or original minimal-Model budgets.
"""
from fractions import Fraction as Q
from itertools import combinations
import json
import sys


def rational(value):
    if isinstance(value, bool) or not isinstance(value, (int, str)):
        raise ValueError('Exact rational integer/string required; floats rejected')
    return Q(value)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify(model):
    require(type(model.get('n')) is int and model['n'] == 4, 'n must be4')
    heavy = model.get('heavy')
    require(type(heavy) is int and heavy in (0, 5), 'heavy must be endpoint0 or5')
    delta = rational(model['delta'])
    require(Q(1, 2) <= delta < 1, 'HIGH delta range failed')
    require(len(model['theta']) == 6, 'all six theta values required')
    theta = list(map(rational, model['theta']))
    require(all(0 <= t <= delta for t in theta), 'theta bound failed')
    require(all(a < b for a, b in zip(theta, theta[1:])), 'strict fan order failed')
    edges = list(combinations(range(6), 2))
    keys = {f'{i},{j}' for i, j in edges}
    require(set(model['d']) == keys, 'exactly15 shared off-diagonal chords required')
    d = {(i, j): rational(model['d'][f'{i},{j}']) for i, j in edges}
    chord = lambda i, j: d[tuple(sorted((i, j)))]
    for (i, j), value in d.items():
        require(theta[i] + 1 <= value <= 3 + delta + theta[j],
                f'corridor failed at{i},{j}')
    bits = []
    for i, j, k in combinations(range(6), 3):
        x, y, z = chord(i, j), chord(i, k), chord(j, k)
        low = x + 1 <= z and x < y < z
        high = z + 1 <= x and z < y < x
        require(low or high, f'triangle failed at{i},{j},{k}')
        require(not (low and high), 'triangle arms must be exclusive')
        bits.append(int(high))
    require(len(bits) == 20, 'all20 triangles required')
    period = 4 + delta
    rows, orders, all_floors = [], [], []
    for i in range(6):
        order = sorted((j for j in range(6) if j != i), key=lambda j: (chord(i, j), j))
        xs = [chord(i, j) for j in order]
        require(len(xs) == 5 and len(set(order)) == 5 and i not in order,
                'complete punctured row required')
        gaps = [xs[0] - theta[i]] + [b-a for a,b in zip(xs,xs[1:])] + [theta[i]+period-xs[-1]]
        require(len(gaps) == 6 and all(g >= 0 for g in gaps), f'gap invalid at row{i}')
        require(sum(gaps) == period, f'full endpoints omitted at row{i}')
        floors = [g.numerator // g.denominator for g in gaps]
        require(all(0 <= q <= 4 for q in floors), f'floor outside exact n4 range at row{i}')
        score = sum(max(q-1,0) for q in floors)
        defect = max(4-score,0)
        require(score <= 4, 'natural-subtraction accounting failure')
        wanted = 2 if i == heavy else 3
        require(defect == wanted, f'full actual floor defect mismatch at row{i}: {defect}!={wanted}')
        orders.append(order);all_floors.append(floors)
        rows.append({'row':i,'order':order,'rowxs':list(map(str,xs)),
                     'gaps':list(map(str,gaps)),'floors':floors,'score':score,'defect':defect})
    anchor_gaps = [b-a for a,b in zip(theta,theta[1:])] + [theta[0]+period-theta[-1]]
    anchor_score = sum(max(g.numerator//g.denominator-1,0) for g in anchor_gaps)
    require(sum(anchor_gaps) == period and anchor_score == 3, 'implicit saturated-anchor fan failed')
    if 'word_bits' in model:
        require(model['word_bits'] == bits, 'claimed word differs from actual triangle branches')
    if 'row_orders' in model:
        require(model['row_orders'] == orders, 'claimed row orders differ from full actual sorting')
    if 'rowxs' in model:
        require([[rational(x) for x in row] for row in model['rowxs']] == [[rational(x) for x in row['rowxs']] for row in rows], 'solver row entries differ from actual complete sorting')
    if 'gaps' in model:
        require([[rational(x) for x in row] for row in model['gaps']] == [[rational(x) for x in row['gaps']] for row in rows], 'solver gaps differ from actual full endpoint gaps')
    if 'floors' in model:
        require(model['floors'] == all_floors, 'solver floor variables differ from actual floors')
    weight = 2**anchor_score + sum(2**row['score'] for row in rows)
    require(weight == 22, 'full scalar profile weight must be22')
    return {'status':'EXACT_RATIONAL_SCALAR_SAT_VERIFIED','model_type':'GenericModel6 4',
            'delta':str(delta),'theta':list(map(str,theta)),
            'chords':{f'{i},{j}':str(v) for (i,j),v in d.items()},
            'triangle_count':20,'word_bits':bits,'word_little_endian':sum(b<<i for i,b in enumerate(bits)),
            'row_count':6,'floors_checked':36,'rows':rows,'heavy':heavy,
            'anchor_gaps':list(map(str,anchor_gaps)),'anchor_score':anchor_score,'profile_weight':weight,
            'full_sorted_row_multisets_checked':True,'all_corridors_and_triangles_checked':True,
            'physical_point_realizability':'NOT_CLAIMED','minimal_countermodel_deletion_caps':'NOT_CHECKED',
            'Lean_certificate':False}


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: verify_n4_r1_positive_seven_scalar_20261008.py candidate.json')
    with open(sys.argv[1]) as handle:
        model = json.load(handle)
    print(json.dumps(verify(model), indent=2))
