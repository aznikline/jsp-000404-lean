"""Full re-verification with consistent cyclic convention:
enumerate int-feasible s=4 assignments, filter LP-feasible,
test joint cert (exists t + carry subset: LP-feasible in s-system,
merged fully feasible, cert inequality)."""
import sys
from fractions import Fraction as Fr
from del_lp2 import all_int_assignments
from del_lp import base_rows, lp_solve
from joint_cert import joint_cert

n = int(sys.argv[1])
d = Fr(int(sys.argv[2]), int(sys.argv[3]))
s = 4
nv = s * (s - 1)
aa = all_int_assignments(s, n, d)
feas = [a for a in aa if lp_solve(base_rows(a, n, s, d), nv)]
print('n=%d d=%s: int=%d LP-feasible=%d' % (n, d, len(aa), len(feas)),
      flush=True)
bad = 0
for idx, a in enumerate(feas):
    t, mode = joint_cert(a, n, s, d)
    if t is None:
        bad += 1
        print('   NO-JOINT-CERT %s' % (a,), flush=True)
    if idx % 200 == 0:
        print('   ...%d/%d' % (idx, len(feas)), flush=True)
print('   feasible without joint cert: %d / %d' % (bad, len(feas)),
      flush=True)
