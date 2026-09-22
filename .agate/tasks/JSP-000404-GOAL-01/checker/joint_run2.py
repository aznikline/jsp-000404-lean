"""Refined: do all NO-JOINT-CERT feasible assignments have F <= cap?
Track F distribution of failures."""
import sys
from fractions import Fraction as Fr
from del_lp2 import all_int_assignments
from del_lp import base_rows, lp_solve
from joint_cert import joint_cert


def Fof(a):
    return sum(2 ** sum(max(m - 1, 0) for m in v) for v in a)


n = int(sys.argv[1])
d = Fr(int(sys.argv[2]), int(sys.argv[3]))
cap = 2 ** n + (2 ** (n - 2) if d >= Fr(1, 2) else 0)
s = 4
nv = s * (s - 1)
aa = all_int_assignments(s, n, d)
feas = [a for a in aa if lp_solve(base_rows(a, n, s, d), nv)]
print('n=%d d=%s: int=%d LP-feasible=%d cap=%d'
      % (n, d, len(aa), len(feas), cap), flush=True)
bad_low = 0
bad_high = 0
maxF = 0
for a in feas:
    F = Fof(a)
    maxF = max(maxF, F)
    t, mode = joint_cert(a, n, s, d)
    if t is None:
        if F > cap - 4:
            bad_high += 1
            print('   HIGH-F NO-CERT F=%d %s' % (F, a), flush=True)
        else:
            bad_low += 1
print('   maxF=%d, no-cert F<=cap-4: %d, no-cert F>cap-4: %d'
      % (maxF, bad_low, bad_high), flush=True)
