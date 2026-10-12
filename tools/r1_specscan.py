#!/usr/bin/env python3
"""Find minimal UNSAT row-subset per R1 terminal combo (class-free sigs).

Profiles: (name, P, defects of non-anchor rows by rank assignment).
For each defect assignment, greedily drop rows while UNSAT is preserved.
Output JSON: {name: {'combo': spec}} spec = sorted [(rank, kind)].
"""
import sys, os, json, itertools, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from r1_msig import build_solver, is_unsat
import z3

# (name, P, counts): total non-anchor rows P; defects: n2 defect-2 (always 1),
# n3 defect-3 (s1), n4 defect-4 (s0); n3 + n4 = P - 1.
PROFILES = [
    ('T1', 6, 5, 0),
    ('T2', 6, 4, 1),
    ('T3', 7, 3, 3),
    ('T4', 8, 2, 5),
    ('T5', 9, 1, 7),
    ('T6', 10, 0, 9),
]


def combos(P, n3, n4):
    """yield (a, s1ranks, s0ranks): a = defect-2 rank."""
    for a in range(P):
        rest = [r for r in range(P) if r != a]
        for s1s in itertools.combinations(rest, n3):
            s0s = tuple(r for r in rest if r not in s1s)
            yield a, s1s, s0s


def minimize(P, spec):
    """Greedy row-deletion to a minimal UNSAT subset."""
    spec = sorted(spec)
    if not is_unsat(P, spec):
        return None
    improved = True
    while improved:
        improved = False
        for row in list(spec):
            cand = [x for x in spec if x != row]
            if cand and is_unsat(P, cand):
                spec = cand
                improved = True
                break
    return spec


def main():
    out = {}
    path = os.path.join(HERE, 'r1_specs.json')
    for name, P, n3, n4 in PROFILES:
        t0 = time.time()
        res = {}
        for a, s1s, s0s in combos(P, n3, n4):
            full = ([(a, 's2')] + [(r, 's1') for r in s1s]
                    + [(r, 's0') for r in s0s])
            key = f'a{a}_s1{",".join(map(str, s1s))}_s0{",".join(map(str, s0s))}'
            spec = minimize(P, full)
            res[key] = spec
            if spec is None:
                print(f'  {name} {key}: SAT?!', flush=True)
        out[name] = res
        json.dump(out, open(path, 'w'))
        uniq = {tuple(v) for v in res.values() if v}
        print(f'{name}: {len(res)} combos -> {len(uniq)} unique specs '
              f'({time.time()-t0:.0f}s)', flush=True)
    print('done ->', path, flush=True)


if __name__ == '__main__':
    main()
