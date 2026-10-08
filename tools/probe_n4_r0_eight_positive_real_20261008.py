#!/usr/bin/env python3
"""SOURCE_ONLY single m7/n4 all-positive QF_LRA probe; await run grant.

Seven full rows, 21 corridors, 35 triangle alternatives; no gauge, heavy,
integer-floor variables, exact-profile equality, or caller potential premise.
"""
from pathlib import Path
from itertools import combinations
import hashlib, json, resource, time
import probe_n4_r1_positive_seven_scalar_20261008 as guard

ROOT = Path(__file__).resolve().parents[1]


def worker(out):
    import z3
    from verify_n4_r0_eight_positive_real_20261008 import verify
    resource.setrlimit(resource.RLIMIT_CPU, (105, 105))
    for name in (Path(__file__).name, 'verify_n4_r0_eight_positive_real_20261008.py'):
        (out/name).write_bytes((ROOT/'tools'/name).read_bytes())
    solver = z3.SolverFor('QF_LRA'); solver.set(timeout=95000, random_seed=0)
    delta = z3.Real('delta'); theta = [z3.Real(f'theta{i}') for i in range(7)]
    edges = list(combinations(range(7), 2))
    d = {edge: z3.Real(f'd{edge[0]}{edge[1]}') for edge in edges}
    chord = lambda i, j: d[tuple(sorted((i, j)))]
    solver.add(delta >= z3.RealVal('1/2'), delta < 1)
    for i, value in enumerate(theta):
        solver.add(value >= 0, value <= delta)
        if i < 6: solver.add(value < theta[i+1])
    for (i, j), value in d.items(): solver.add(theta[i]+1 <= value, value <= 3+delta+theta[j])
    arms = []
    for i, j, k in combinations(range(7), 3):
        x, y, z = chord(i, j), chord(i, k), chord(j, k)
        low = z3.And(x+1 <= z, x < y, y < z)
        high = z3.And(z+1 <= x, z < y, y < x)
        solver.add(z3.Or(low, high)); arms.append(high)
    xsrows, gaprows = [], []
    for i in range(7):
        xs = [chord(i, j) for j in range(7) if j != i]
        # Six-entry bubble sorting network: fifteen fixed comparators.
        for end in range(5, 0, -1):
            for a in range(end):
                x, y = xs[a], xs[a+1]
                xs[a], xs[a+1] = z3.If(x <= y, x, y), z3.If(x <= y, y, x)
        gaps = [xs[0]-theta[i]]+[b-a for a, b in zip(xs, xs[1:])]+[theta[i]+4+delta-xs[-1]]
        solver.add(*[gap >= 0 for gap in gaps])
        solver.add(z3.Or(*[gap >= 2 for gap in gaps]))
        xsrows.append(xs); gaprows.append(gaps)
    (out/'problem.smt2').write_text(solver.sexpr())
    begin = time.monotonic(); status = solver.check()  # Exactly one check.
    record = {'status': str(status), 'solver_seconds': time.monotonic()-begin,
              'logic': 'QF_LRA', 'integer_variables': 0, 'm': 7, 'n': 4,
              'positive_rows': list(range(7)), 'delta_range': '1/2<=delta<1',
              'triangles': 35, 'corridors': 21, 'full_rows': 7, 'full_gaps': 49,
              'positive_profile_alternatives_per_row': 7, 'solver_checks': 1,
              'gauge_constraint': False, 'exact_R0_profile_claimed': False, 'Lean_proof': False}
    (out/'result.json').write_text(json.dumps(record, indent=2)+'\n')
    if status == z3.sat:
        model = solver.model(); (out/'solver-model.raw.smt2').write_text(model.sexpr())
        def qstr(expression):
            value = model.eval(expression, model_completion=True)
            if not z3.is_rational_value(value): raise ValueError('Non-rational model value')
            return str(value.numerator_as_long())+'/'+str(value.denominator_as_long())
        raw = {'m': 7, 'n': 4, 'positive_rows': list(range(7)), 'delta': qstr(delta),
               'theta': [qstr(value) for value in theta], 'd': {f'{i},{j}': qstr(value) for (i, j), value in d.items()},
               'word_bits': [int(z3.is_true(model.eval(arm))) for arm in arms],
               'rowxs': [[qstr(value) for value in row] for row in xsrows],
               'gaps': [[qstr(value) for value in row] for row in gaprows]}
        (out/'candidate.raw.json').write_text(json.dumps(raw, indent=2)+'\n')
        checked = verify(raw)
        (out/'candidate.verified.json').write_text(json.dumps(checked, indent=2)+'\n')
        record['status'] = checked['status']
        for name in ('candidate.raw.json', 'candidate.verified.json'):
            record[name+'_sha256'] = hashlib.sha256((out/name).read_bytes()).hexdigest()
    elif status == z3.unknown: record['reason'] = solver.reason_unknown()
    else: record['interpretation'] = 'UNSAT solver diagnostic only, not a Lean proof'
    (out/'result.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps(record), flush=True)


if __name__ == '__main__':
    guard.worker = worker; guard.__file__ = __file__
    guard.main()  # Frozen95s solver /110+5s wall /512MiB process-tree guard.
