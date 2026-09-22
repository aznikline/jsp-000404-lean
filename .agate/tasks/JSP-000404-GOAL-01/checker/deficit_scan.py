"""Maximize the deficit  F - wE  over LP-feasible assignments.
Weak inequality needs deficit <= s-1.  Scan n=3,4,5 and s=4,5."""
import itertools, random, sys
from fractions import Fraction as Fr
from del_lp import base_rows, lp_solve
from del_lp2 import all_int_assignments
from emission_analyze import adj_pairs, pair_data, max_emission
import weighted_lp as W


def scan(n, s, d, Fmin, limit):
    nv = s * (s - 1)
    aa = all_int_assignments(s, n, d)
    random.shuffle(aa)
    tested = 0
    worst = -10 ** 9
    worst_a = None
    for a in aa:
        if tested >= limit:
            break
        F = sum(2 ** sum(max(m - 1, 0) for m in v) for v in a)
        if F < Fmin:
            continue
        if not W.int_constraints_ok(a, n, d, s):
            continue
        if not lp_solve(base_rows(a, n, s, d), nv):
            continue
        tested += 1
        wE, S, ks, _ = max_emission(a, n, s, d)
        deficit = F - wE
        if deficit > worst:
            worst, worst_a = deficit, (a, ks, F, wE)
    print('n=%d s=%d d=%s: tested=%d max-deficit=%d (slack s-1=%d) %s'
          % (n, s, d, tested, worst, s - 1, worst_a), flush=True)


random.seed(3)
scan(3, 4, Fr(1, 4), 7, 3000)
scan(4, 4, Fr(1, 4), 14, 400)
scan(4, 4, Fr(3, 4), 14, 400)
scan(5, 4, Fr(1, 4), 28, 200)
scan(4, 5, Fr(1, 4), 13, 150)
scan(4, 5, Fr(3, 4), 16, 150)
