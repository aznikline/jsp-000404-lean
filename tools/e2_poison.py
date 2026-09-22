"""Lane E2 — lane_a6._CAP_CACHE id(ctx) poisoning test.

lane_a6.cap_options_ext caches Pareto cap options under key
(id(ctx), v, negblk, maxsz).  Ctx objects are created per call and
freed afterwards; CPython may reuse the freed id for the NEXT
skeleton's Ctx.  If the same (v, negblk, maxsz) key then hits, the
evaluator returns cap options computed from a DIFFERENT skeleton's
angle data -> wrong (possibly overcertifying) bound.

Test: in one process, run enumerate_max_ext over a stream of
skeletons WITHOUT clearing the cache (the natural usage pattern),
then re-run each with a cleared cache.  Any bound difference is a
demonstrated poisoning; a poisoned bound > free_min is a live
overcertification.

Usage: python3 e2_poison.py s count [seed] [maxsz]
"""
import sys, gc, json, time, random
sys.path.insert(0, '.')
from fractions import Fraction as F
import lane_e_util as le
import e2_util as e2
import lane_a6


def main():
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    maxsz = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    n = s
    rng = random.Random(seed)
    profs = [d for d in le.deficit_profiles(n, s)
             if le.W_of_d(d) > 2]
    sols = []
    while len(sols) < count:
        d = profs[rng.randrange(len(profs))]
        ks = le.ks_of_d(n, d)
        VV = le.ge.build_VV(ks, n, s)
        sigvars = le.ge.build_sigvars(VV, s)
        for sol, idxs, sk in le.ge.gen_cases(ks, n, s, VV=VV,
                                             sigvars=sigvars):
            sols.append((d, le.sol_to_data(sol)))
            if len(sols) >= count:
                break
    print('stream of %d skeletons, s=%d' % (len(sols), s), flush=True)
    diffs = []
    t0 = time.time()
    for i, (d, sdat) in enumerate(sols):
        sol = le.data_to_sol(sdat, n)
        # natural usage: warm cache (never cleared between skeletons)
        b_warm = lane_a6.enumerate_max_ext(sol, n, s, maxsz=maxsz)
        del sol
        gc.collect()                      # encourage id reuse
        sol = le.data_to_sol(sdat, n)
        lane_a6._CAP_CACHE.clear()
        b_cold = lane_a6.enumerate_max_ext(sol, n, s, maxsz=maxsz)
        if b_warm != b_cold:
            mm = e2.mins_exact(sol, n)
            diffs.append(dict(d=list(d), i=i, warm=str(b_warm),
                              cold=str(b_cold), sol=sdat,
                              capped=str(mm['capped']),
                              relaxed=str(mm['relaxed']),
                              free=str(mm['free'])))
            print('*** POISON i=%d d=%s warm=%s cold=%s '
                  'relaxed=%s free=%s'
                  % (i, d, b_warm, b_cold, mm['relaxed'],
                     mm['free']), flush=True)
        if i % 5 == 0:
            print('  %d/%d (%.0fs) diffs=%d cache=%d'
                  % (i, len(sols), time.time() - t0, len(diffs),
                     len(lane_a6._CAP_CACHE)), flush=True)
    print('\ndiffs=%d / %d' % (len(diffs), len(sols)))
    json.dump(diffs, open('e2_poison_s%d.json' % s, 'w'), indent=1)


if __name__ == '__main__':
    main()
