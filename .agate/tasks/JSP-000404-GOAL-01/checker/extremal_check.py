"""Verify: every feasible assignment has a cert at a min-k OR max-k
vertex (extremal rule)."""
import itertools, random, sys
from fractions import Fraction as Fr
from del_lp import base_rows, lp_solve
from del_lp2 import all_int_assignments
from joint_cert import flank_pair
import weighted_lp as W


def cert_set(assign, n, s, d):
    """set of t with a cert (auto or feasible-carry)."""
    nv = s * (s - 1)
    rows0 = base_rows(assign, n, s, d)
    ks = [sum(max(m - 1, 0) for m in v) for v in assign]
    good = set()
    for t in range(s):
        need = 2 ** ks[t]
        autos = {}
        cand = []
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
            good.add(t)
            continue
        found = False
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
            good.add(t)
    return good, ks


def scan(n, s, d, Fmin, limit):
    nv = s * (s - 1)
    tested = fail = 0
    for a in all_int_assignments(s, n, d):
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
        good, ks = cert_set(a, n, s, d)
        ext = {v for v in range(s) if ks[v] == min(ks) or ks[v] == max(ks)}
        if not (good & ext):
            fail += 1
            print('EXTREMAL-FAIL ks=%s cert@=%s a=%s' % (ks, sorted(good), a),
                  flush=True)
        elif not good:
            print('NO-CERT ks=%s a=%s' % (ks, a), flush=True)
    print('n=%d s=%d d=%s Fmin=%d tested=%d extremal-fail=%d'
          % (n, s, d, Fmin, tested, fail), flush=True)


if __name__ == '__main__':
    scan(3, 4, Fr(1, 4), 7, 600)
    scan(4, 4, Fr(1, 4), 15, 600)
    scan(4, 4, Fr(3, 4), 15, 600)
