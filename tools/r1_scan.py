#!/usr/bin/env python3
"""R1 boundary-profile coverage scan (pure-LRA successor-gap model).

For each of the six R1 boundary profiles at n=4, check that the scalar
model is UNSAT for EVERY rank assignment of the defect-3 rows (defect-4
rows enter as sig0 all-gaps-<2 constraints; the defect-2 row as sig2).

  T1: (1,2,3,3,3,3,3)         t=7   P=6   s2 + 5 s1
  T2: (1,2,3,3,3,3,4)         t=7   P=6   s2 + 4 s1 + 1 s0
  T3: (1,2,3,3,3,4,4,4)       t=8   P=7   s2 + 3 s1 + 3 s0
  T4: (1,2,3,3,4,4,4,4,4)     t=9   P=8   s2 + 2 s1 + 5 s0
  T5: (1,2,3,4,4,4,4,4,4,4)   t=10  P=9   s2 + 1 s1 + 7 s0
  T6: (1,2,4,4,4,4,4,4,4,4,4) t=11  P=10  s2 + 9 s0
"""
import sys, itertools, time, json
sys.path.insert(0, 'tools')
import s7_model
from r1_lin_model import sig0, sig1, sig2, check

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
    t0 = time.time(); unsat = sat = unk = 0; bad = []
    for a in range(P):
        others = [r for r in range(P) if r != a]
        for comb in itertools.combinations(others, k):
            r = check(P, a, comb)
            if r == 'unsat': unsat += 1
            elif r == 'sat': sat += 1; bad.append(('sat', a, comb))
            else: unk += 1; bad.append(('unk', a, comb))
    results[name] = dict(P=P, k=k, unsat=unsat, sat=sat, unk=unk,
                         dt=round(time.time()-t0,1), bad=bad[:30])
    print(f'{name}: unsat={unsat} sat={sat} unk={unk} '
          f'({time.time()-t0:.0f}s)', flush=True)
    if bad:
        print('   ', bad[:10], flush=True)

json.dump(results, open('tools/r1_scan_results.json', 'w'), indent=1)
print('done')
