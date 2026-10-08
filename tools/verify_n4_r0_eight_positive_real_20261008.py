#!/usr/bin/env python3
"""Independent exact-Fraction m7/n4 all-positive weak scalar verifier.

No solver/search or encoder import. All 49 full-row floors are recomputed.
No exact R0 profile, weight22, planar realization, or minimal Model is assumed.
"""
from fractions import Fraction as Q
from itertools import combinations
import json, sys


def rational(value):
    if isinstance(value, bool) or not isinstance(value, (int, str)):
        raise ValueError('Exact integer/string rational required; floats rejected')
    return Q(value)


def require(condition, message):
    if not condition: raise ValueError(message)


def verify(model):
    require(type(model.get('n')) is int and model['n'] == 4, 'n must be4')
    require(type(model.get('m')) is int and model['m'] == 7, 'm must be7')
    require(model.get('positive_rows') == list(range(7)), 'all seven positive rows required')
    delta = rational(model['delta'])
    require(Q(1, 2) <= delta < 1, 'HIGH delta range failed')
    theta = list(map(rational, model['theta']))
    require(len(theta) == 7 and all(0 <= t <= delta for t in theta), 'all seven theta bounds required')
    require(all(a < b for a, b in zip(theta, theta[1:])), 'strict fan order failed')
    edges = list(combinations(range(7), 2))
    require(set(model['d']) == {f'{i},{j}' for i, j in edges}, 'exactly21 shared chords required')
    d = {(i, j): rational(model['d'][f'{i},{j}']) for i, j in edges}
    chord = lambda i, j: d[tuple(sorted((i, j)))]
    for (i, j), value in d.items():
        require(theta[i]+1 <= value <= 3+delta+theta[j], f'corridor failed at{i},{j}')
    bits = []
    for i, j, k in combinations(range(7), 3):
        x, y, z = chord(i, j), chord(i, k), chord(j, k)
        low, high = x+1 <= z and x < y < z, z+1 <= x and z < y < x
        require(low or high, f'triangle failed at{i},{j},{k}')
        require(not (low and high), 'triangle alternatives must be exclusive')
        bits.append(int(high))
    require(len(bits) == 35, 'all35 triangle alternatives required')
    period, rows = 4+delta, []
    for i in range(7):
        order = sorted((j for j in range(7) if j != i), key=lambda j: (chord(i, j), j))
        xs = [chord(i, j) for j in order]
        require(len(xs) == 6 and len(set(order)) == 6 and i not in order, 'full six-chord row required')
        gaps = [xs[0]-theta[i]]+[b-a for a, b in zip(xs, xs[1:])]+[theta[i]+period-xs[-1]]
        require(len(gaps) == 7 and all(g >= 0 for g in gaps), f'full gap nonnegativity failed at row{i}')
        require(sum(gaps) == period, f'full endpoint accounting failed at row{i}')
        floors = [g.numerator//g.denominator for g in gaps]
        require(all(0 <= q <= 4 for q in floors), f'actual floor range failed at row{i}')
        score = sum(max(q-1, 0) for q in floors)
        require(score >= 1, f'positive actual score failed at row{i}')
        require((score >= 1) == any(g >= 2 for g in gaps), 'positive-profile equivalence failed')
        rows.append({'row': i, 'order': order, 'rowxs': list(map(str, xs)), 'gaps': list(map(str, gaps)),
                     'floors': floors, 'score': score, 'defect': max(4-score, 0)})
    if 'word_bits' in model: require(model['word_bits'] == bits, 'claimed word differs from exact triangle arms')
    for key in ('rowxs', 'gaps'):
        if key in model:
            require([[rational(x) for x in row] for row in model[key]] ==
                    [[rational(x) for x in row[key]] for row in rows], f'claimed {key} differs from full actual rows')
    if 'floors' in model: require(model['floors'] == [row['floors'] for row in rows], 'claimed floors differ from recomputed floors')
    anchor_gaps = [b-a for a, b in zip(theta, theta[1:])]+[theta[0]+period-theta[-1]]
    require(len(anchor_gaps) == 7 and all(g >= 0 for g in anchor_gaps), 'full anchor gaps failed')
    anchor_score = sum(max(g.numerator//g.denominator-1, 0) for g in anchor_gaps)
    require(sum(anchor_gaps) == period and anchor_score == 3, 'saturated anchor score failed')
    return {'status': 'WEAK_SAT_EXACT_RATIONAL_M7_ALL_POSITIVE_VERIFIED', 'model_type': 'GenericModel7 4',
            'delta': str(delta), 'theta': list(map(str, theta)), 'chords': {f'{i},{j}': str(v) for (i, j), v in d.items()},
            'triangle_count': 35, 'corridor_count': 21, 'word_bits': bits,
            'word_little_endian': sum(bit << i for i, bit in enumerate(bits)), 'rows': rows,
            'floors_checked': 49, 'anchor_gaps': list(map(str, anchor_gaps)), 'anchor_score': anchor_score,
            'profile_weight_diagnostic_only': 2**anchor_score+sum(2**row['score'] for row in rows),
            'exact_R0_profile_claimed': False, 'physical_point_realizability': 'NOT_CLAIMED',
            'original_minimal_model_caps': 'NOT_CHECKED', 'Lean_proof': False}


if __name__ == '__main__':
    if len(sys.argv) != 2: raise SystemExit('usage: verify_n4_r0_eight_positive_real_20261008.py candidate.json')
    print(json.dumps(verify(json.loads(open(sys.argv[1]).read())), indent=2))
