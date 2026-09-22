from del_lp2 import all_int_assignments, flank_pair, cert_exists_fast
from del_lp import base_rows, lp_solve
from fractions import Fraction as Fr
import sys


def auto_cert_only(assign, s):
    ks = [sum(max(m - 1, 0) for m in a) for a in assign]
    for t in range(s):
        need = 2 ** ks[t]
        inc = 0
        for i in range(s):
            if i == t:
                continue
            ga, gb = flank_pair(i, t, s)
            if assign[i][ga] >= 1 and assign[i][gb] >= 1:
                inc += 2 ** ks[i]
        if inc >= need:
            return True
    return False


def run(n, d, s=4):
    nv = s * (s - 1)
    aa = all_int_assignments(s, n, d)
    hard = [a for a in aa if not auto_cert_only(a, s)]
    feas = [a for a in hard if lp_solve(base_rows(a, n, s, d), nv)]
    print('n=%d d=%s s=%d: int=%d no-auto=%d hard-feas=%d'
          % (n, d, s, len(aa), len(hard), len(feas)), flush=True)
    bad = 0
    for idx, a in enumerate(feas):
        ks, res = cert_exists_fast(a, n, s, d)
        if not any(r[3] for r in res):
            bad += 1
            print('   NO-CERT %s ks=%s' % (a, ks), flush=True)
    print('   without cert: %d' % bad, flush=True)


run(int(sys.argv[1]), Fr(int(sys.argv[2]), int(sys.argv[3])),
    int(sys.argv[4]) if len(sys.argv) > 4 else 4)
