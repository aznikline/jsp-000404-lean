"""For each high-F feasible assignment, find ALL cert vertices (with some
feasible carry set giving cert at that t) and record their k-levels,
plus which vertices are forced zero-emitters (B_v < 1)."""
import sys
from fractions import Fraction as Fr
from del_lp import base_rows, lp_solve
from joint_cert import flank_pair, merged_assign, full_int_ok
from emission_analyze import adj_pairs, pair_data
from del_lp2 import all_int_assignments
import weighted_lp as W

n, d, s = 3, Fr(1, 4), 4
nv = s * (s - 1)
Fmin = int(sys.argv[1]) if len(sys.argv) > 1 else 7

def cert_vertices(assign):
    """Return set of t for which some feasible carry subset gives
    G_t >= 2^{k_t} (carry restricted to i's own flank pair is enough:
    carry at flank pair (a,b) of dir(i->t) affects only g_{it})."""
    rows0 = base_rows(assign, n, s, d)
    ks = [sum(max(m - 1, 0) for m in v) for v in assign]
    good = {}
    for t in range(s):
        need = 2 ** ks[t]
        # candidate single-pair carries that can feed t
        cand = []
        for i in range(s):
            if i == t:
                continue
            ga, gb = flank_pair(i, t, s)
            ma, mb = assign[i][ga], assign[i][gb]
            if ma >= 1 or mb >= 1:
                cand.append((i, i * (s - 1) + ga, i * (s - 1) + gb, ga, gb))
        autos = {}
        for i in range(s):
            if i == t:
                continue
            ga, gb = flank_pair(i, t, s)
            autos[i] = 1 if (assign[i][ga] >= 1 and assign[i][gb] >= 1) else 0
        inc0 = sum((2 ** ks[i]) * (2 ** autos[i] - 1) for i in range(s) if i != t)
        if inc0 >= need:
            good[t] = 'auto'
            continue
        # enumerate subsets of cand
        found = None
        for sz in range(1, len(cand) + 1):
            import itertools
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
                    found = [p[0] for p in sub]
                    break
            if found is not None:
                break
        if found is not None:
            good[t] = 'carries@' + ','.join(map(str, found))
    return good, ks

neg = tested = 0
mink_cert = 0
khist = {}
for a in all_int_assignments(s, n, d):
    F = sum(2 ** sum(max(m - 1, 0) for m in v) for v in a)
    if F < Fmin:
        continue
    if not W.int_constraints_ok(a, n, d, s):
        continue
    if not lp_solve(base_rows(a, n, s, d), nv):
        continue
    tested += 1
    good, ks = cert_vertices(a)
    if not good:
        neg += 1
        print('NO CERT: %s' % (a,))
        continue
    mink = min(ks)
    if mink in [ks[t] for t in good]:
        mink_cert += 1
    key = tuple(sorted(set(ks[t] for t in good)))
    khist[key] = khist.get(key, 0) + 1
print('tested=%d no-cert=%d min-k-has-cert=%d' % (tested, neg, mink_cert))
print('cert-k-level histogram:', khist)
