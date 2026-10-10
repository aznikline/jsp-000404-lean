#!/usr/bin/env python3
"""R1 terminal-profile coverage scan.

For each of the six R1 boundary profiles at n=4, check that the weak
scalar model is UNSAT for EVERY rank assignment of the defect-3 rows
(defect-4 rows enter as sig_score0 constraints).

  T1: (1,2,3,3,3,3,3)        t=7   P=6  s2 + 5 s1
  T2: (1,2,3,3,3,3,4)        t=7   P=6  s2 + 4 s1 + 1 s0
  T3: (1,2,3,3,3,4,4,4)      t=8   P=7  s2 + 3 s1 + 3 s0
  T4: (1,2,3,3,4,4,4,4,4)    t=9   P=8  s2 + 2 s1 + 5 s0
  T5: (1,2,3,4,4,4,4,4,4,4)  t=10  P=9  s2 + 1 s1 + 7 s0
  T6: (1,2,4,4,4,4,4,4,4,4,4) t=11  P=10 s2 + 9 s0
"""
import sys, itertools, time, json
sys.path.insert(0, 'tools')
import s7_model, z3

z3.set_param('smt.random_seed', 0)

def sig_score0(gaps):
    return z3.And(*[g < 2 for g in gaps])

def check(P, a_rank, s1_ranks, timeout=90000):
    """a = defect-2 rank; s1_ranks = defect-3 ranks; rest defect-4."""
    delta, t, d, D, p, base, trips = s7_model.build(P)
    s = z3.Solver(); s.set('timeout', timeout)
    s.add(base)
    for tr in trips.values():
        s.add(tr)
    s1set = set(s1_ranks)
    for r in range(P):
        cons, gaps = s7_model.row_gaps(r, P, t[r], D, p)
        s.add(cons)
        if r == a_rank:
            s.add(s7_model.sig_score2(gaps))
        elif r in s1set:
            s.add(s7_model.sig_score1(gaps))
        else:
            s.add(sig_score0(gaps))
    return str(s.check())

PROFILES = [
    ('T1_P6_3all', 6, 5),
    ('T2_P6_34',   6, 4),
    ('T3_P7_333',  7, 3),
    ('T4_P8_33',   8, 2),
    ('T5_P9_3',    9, 1),
    ('T6_P10_all4', 10, 0),
]

results = {}
for name, P, k in PROFILES:
    t0 = time.time()
    unsat, sat, unk = 0, 0, 0
    sat_cases, unk_cases = [], []
    for a in range(P):
        others = [r for r in range(P) if r != a]
        for comb in itertools.combinations(others, k):
            r = check(P, a, comb)
            if r == 'unsat':
                unsat += 1
            elif r == 'sat':
                sat += 1; sat_cases.append((a, comb))
            else:
                unk += 1; unk_cases.append((a, comb))
    dt = time.time() - t0
    results[name] = dict(P=P, k=k, unsat=unsat, sat=sat, unknown=unk,
                         dt=dt, sat_cases=sat_cases[:20],
                         unk_cases=unk_cases[:20])
    print(f'{name}: P={P} k={k}  unsat={unsat} sat={sat} unk={unk}  ({dt:.0f}s)',
          flush=True)
    if sat_cases:
        print(f'   SAT cases: {sat_cases[:10]}', flush=True)
    if unk_cases:
        print(f'   UNK cases: {unk_cases[:10]}', flush=True)

with open('tools/r1_scan_results.json', 'w') as f:
    json.dump(results, f, indent=1)
print('done')
