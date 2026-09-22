import itertools, random, sys
from fractions import Fraction as Fr
from del_lp import base_rows, lp_solve
from del_lp2 import all_int_assignments
from emission_analyze import adj_pairs, pair_data, max_emission
import weighted_lp as W

n, s, d, Fmin = 3, 4, Fr(1, 4), 7
nv = s * (s - 1)
tested = viol = 0
worst = 10 ** 9
worst_a = None
for idx, a in enumerate(all_int_assignments(s, n, d)):
    F = sum(2 ** sum(max(m - 1, 0) for m in v) for v in a)
    if F < Fmin:
        continue
    if not W.int_constraints_ok(a, n, d, s):
        continue
    tested += 1
    wE, S, ks, _ = max_emission(a, n, s, d)
    gap = wE - (F - s + 1)
    if gap < worst:
        worst, worst_a = gap, (a, ks, F, wE)
    if gap < 0:
        viol += 1
        print('WEAK-VIOL wE=%d F=%d ks=%s a=%s' % (wE, F, ks, a), flush=True)
print('n=3: tested=%d weak-viol=%d worst-gap=%d %s' % (tested, viol, worst, worst_a), flush=True)
