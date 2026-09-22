"""Test the WEAK global inequality  sum_i 2^{k_i} E_i >= F - s + 1
which suffices for cert existence (integer gap argument)."""
import itertools, random
from fractions import Fraction as Fr
from del_lp import base_rows, lp_solve
from del_lp2 import all_int_assignments
from emission_analyze import adj_pairs, pair_data, max_emission
import weighted_lp as W


def check(n, s, d, Fmin, limit=100000):
    nv = s * (s - 1)
    tested = viol = 0
    worst = 10 ** 9
    worst_a = None
    for a in all_int_assignments(s, n, d):
        F = sum(2 ** sum(max(m - 1, 0) for m in v) for v in a)
        if F < Fmin:
            continue
        if not W.int_constraints_ok(a, n, d, s):
            continue
        if not lp_solve(base_rows(a, n, s, d), nv):
            continue
        tested += 1
        wE, S, ks, _ = max_emission(a, n, s, d)
        gap = wE - (F - s + 1)
        if gap < worst:
            worst, worst_a = gap, (a, ks, F, wE)
        if gap < 0:
            viol += 1
            print('WEAK-VIOL wE=%d F=%d s=%d ks=%s a=%s' % (wE, F, s, ks, a))
        if tested >= limit:
            break
    print('n=%d s=%d d=%s Fmin=%d: tested=%d weak-viol=%d worst-gap=%d %s'
          % (n, s, d, Fmin, tested, viol, worst, worst_a))


check(3, 4, Fr(1, 4), 7)

# n=4: sample
random.seed(2)
nv = 4 * 3
aa = all_int_assignments(4, 4, Fr(1, 4))
random.shuffle(aa)
tested = viol = 0
worst = 10 ** 9
worst_a = None
for a in aa:
    if tested >= 150:
        break
    F = sum(2 ** sum(max(m - 1, 0) for m in v) for v in a)
    if F < 13:
        continue
    if not W.int_constraints_ok(a, 4, Fr(1, 4), 4):
        continue
    if not lp_solve(base_rows(a, 4, 4, Fr(1, 4)), nv):
        continue
    tested += 1
    wE, S, ks, _ = max_emission(a, 4, 4, Fr(1, 4))
    gap = wE - (F - 4 + 1)
    if gap < worst:
        worst, worst_a = gap, (a, ks, F, wE)
    if gap < 0:
        viol += 1
        print('WEAK-VIOL wE=%d F=%d ks=%s a=%s' % (wE, F, ks, a))
print('n=4 sample: tested=%d weak-viol=%d worst-gap=%d %s' % (tested, viol, worst, worst_a))
