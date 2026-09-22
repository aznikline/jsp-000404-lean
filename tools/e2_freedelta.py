"""Lane E2 — free-delta scan over enumerated skeletons.

Enumerate skeletons via gen_cases per profile; for each compute the
float relaxed-min and free-min (HiGHS).  Flag for exact
verification:

  consistent (relaxed < 1) AND free < 1/2   -> T_low kill candidate
  consistent AND W > 5/2 AND free < 1       -> T_high kill candidate
  consistent AND free < 0                    -> negative-delta at W>2

Usage: python3 e2_freedelta.py s n band cap_per_profile [seed]
Writes e2_freedelta_s{S}n{N}_{band}.json
"""
import sys, time, random, json
sys.path.insert(0, '.')
from fractions import Fraction as F
import lane_e_util as le
import e2_util as e2
import generic_enum as ge
import generic_model as gm


def scan(s, n, band, cap, seed):
    rng = random.Random(seed)
    profs = le.deficit_profiles(n, s)
    rows = []
    flagged = []
    t0 = time.time()
    for d in profs:
        W = le.W_of_d(d)
        hi = W > F(5, 2)
        mid = F(2) < W <= F(5, 2)
        if band == 'hi' and not hi:
            continue
        if band == 'mid' and not mid:
            continue
        if band == 'wle2' and W > 2:
            continue
        if band == 'all' and not W > 2:
            continue
        ks = le.ks_of_d(n, d)
        try:
            VV = ge.build_VV(ks, n, s)
            sigvars = ge.build_sigvars(VV, s)
        except Exception as ex:
            rows.append(dict(d=list(d), W=str(W), err=str(ex)))
            continue
        cnt = 0
        ncons = 0
        free_lo = None
        neg_lo = None
        ex_min = None
        for sol, idxs, sk in ge.gen_cases(ks, n, s, VV=VV,
                                          sigvars=sigvars):
            if cnt >= cap:
                break
            cnt += 1
            placed = list(range(s))
            nv, cons, obj = e2.float_cons(sol, placed, s, n,
                                          'relaxed')
            rs, rmin = e2.lp_min_f(nv, cons, obj)
            if rs != 'bounded' or rmin >= 1 - 1e-7:
                continue
            ncons += 1
            nv, cons, obj = e2.float_cons(sol, placed, s, n, 'free')
            fs, fmin = e2.lp_min_f(nv, cons, obj)
            if fs != 'bounded':
                continue
            if free_lo is None or fmin < free_lo:
                free_lo = fmin
                if fmin < 0 and (neg_lo is None or fmin < neg_lo):
                    neg_lo = fmin
            thr = 1.0 if hi else 0.5
            if fmin < thr - 1e-7:
                v = e2.verify_candidate(le.sol_to_data(sol), n, s, d)
                if v['viol']:
                    flagged.append(dict(v, sol=le.sol_to_data(sol)))
                    print('*** %s d=%s free=%s relaxed=%s'
                          % (v['viol'], d, v['free'], v['relaxed']),
                          flush=True)
                elif ex_min is None or (
                        v['free'] is not None
                        and str(v['free']) < str(ex_min)):
                    ex_min = v['free']
        rows.append(dict(d=list(d), W=str(W), tested=cnt,
                         consistent=ncons,
                         free_min_float=free_lo,
                         neg_min_float=neg_lo))
        print('d=%s W=%s tested=%d cons=%d flo=%s neg=%s (%.0fs)'
              % (d, str(W), cnt, ncons, free_lo, neg_lo,
                 time.time() - t0), flush=True)
        json.dump(dict(rows=rows, flagged=flagged),
                  open('e2_freedelta_s%dn%d_%s.json' % (s, n, band),
                       'w'), indent=1, default=str)
    print('\nprofiles=%d flagged=%d (%.0fs)'
          % (len(rows), len(flagged), time.time() - t0))


if __name__ == '__main__':
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    n = int(sys.argv[2]) if len(sys.argv) > 2 else s
    band = sys.argv[3] if len(sys.argv) > 3 else 'all'
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else 3000
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    scan(s, n, band, cap, seed)
