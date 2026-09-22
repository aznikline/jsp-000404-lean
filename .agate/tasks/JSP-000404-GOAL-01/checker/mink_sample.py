import random, itertools, sys
from fractions import Fraction as Fr
from del_lp import base_rows, lp_solve
from del_lp2 import all_int_assignments
from joint_cert import flank_pair
import weighted_lp as W


def cert_vertices(assign, n, s, d):
    nv = s * (s - 1)
    rows0 = base_rows(assign, n, s, d)
    ks = [sum(max(m - 1, 0) for m in v) for v in assign]
    good = {}
    for t in range(s):
        need = 2 ** ks[t]
        cand = []
        autos = {}
        for i in range(s):
            if i == t:
                continue
            ga, gb = flank_pair(i, t, s)
            ma, mb = assign[i][ga], assign[i][gb]
            autos[i] = 1 if (ma >= 1 and mb >= 1) else 0
            if ma >= 1 or mb >= 1:
                cand.append((i, i * (s - 1) + ga, i * (s - 1) + gb, ga, gb))
        inc0 = sum((2 ** ks[i]) * (2 ** autos[i] - 1) for i in range(s) if i != t)
        if inc0 >= need:
            good[t] = 'auto'
            continue
        found = None
        for sz in range(1, len(cand) + 1):
            for sub in itertools.combinations(cand, sz):
                rows = list(rows0)
                for (_, x, y, _, _) in sub:
                    rows.append(({x: Fr(-1), y: Fr(-1)}, Fr(-1)))
                if not lp_solve(rows, nv):
                    continue
                S = set((p[0], p[3], p[4]) for p in sub)
                inc = 0
                for i in range(s):
                    if i == t:
                        continue
                    ga, gb = flank_pair(i, t, s)
                    car = 1 if (i, ga, gb) in S else 0
                    inc += (2 ** ks[i]) * (2 ** (autos[i] + car) - 1)
                if inc >= need:
                    found = True
                    break
            if found:
                break
        if found:
            good[t] = 'carry'
    return good, ks


random.seed(1)
for d in [Fr(1, 4), Fr(3, 4)]:
    n, s = 4, 4
    nv = s * (s - 1)
    aa = all_int_assignments(s, n, d)
    random.shuffle(aa)
    tested = neg = mink_cert = 0
    lowfail = []
    for a in aa:
        if tested >= 300:
            break
        if not W.int_constraints_ok(a, n, d, s):
            continue
        if not lp_solve(base_rows(a, n, s, d), nv):
            continue
        tested += 1
        good, ks = cert_vertices(a, n, s, d)
        if not good:
            neg += 1
            print('NO CERT: %s' % (a,))
            continue
        mink = min(ks)
        if mink in [ks[t] for t in good]:
            mink_cert += 1
        else:
            lowfail.append((a, ks, good))
    print('d=%s tested=%d nocert=%d mink=%d' % (d, tested, neg, mink_cert))
    for a, ks, g in lowfail[:5]:
        print('  min-k-fail: ks=%s assign=%s cert@=%s' % (ks, a, g))
