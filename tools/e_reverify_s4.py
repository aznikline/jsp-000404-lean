"""Lane E — fresh-sample re-verification at s=4 (all 35 profiles).

For every deficit profile, sample skeletons via generic_enum.gen_cases
(yields fresh [dict(x) for x in sol] — safe from the skeleton_enum
in-place mutation bug), run the EXACT LP (glp_min_delta) and the pure
gadget enumerator (enumerate_max), and flag:

  VIOL-T_low : 2 < W, LP feasible, min_delta < 1/2
  VIOL-T_high: 5/2 < W, LP feasible, min_delta < 1
  OVERCOUNT  : gadget bound > LP min_delta (unsound evaluator)
  UNDERCOUNT : gadget bound < LP min_delta (evaluator too weak)

Usage: python3 e_reverify_s4.py [per_profile] [gadgets:0/1]
"""
import sys, itertools, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import lane_e_util as le


def main():
    per_prof = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    do_gadgets = (len(sys.argv) > 2 and sys.argv[2] == '1')
    n = s = 4
    rng_profiles = le.deficit_profiles(n, s)
    stats = {'violation': [], 'overcount': [], 'undercount': [],
             'feas': 0, 'inf': 0, 'nodirect': 0}
    t0 = time.time()
    for d in rng_profiles:
        W = le.W_of_d(d)
        ks = le.ks_of_d(n, d)
        band = ('low' if W <= 2 else 'mid' if W <= F(5, 2)
                else 'high')
        VV = le.ge.build_VV(ks, n, s)
        sigvars = le.ge.build_sigvars(VV, s)
        cnt = feas = 0
        deltas = {}
        for sol, idxs, sk in le.ge.gen_cases(ks, n, s, VV=VV,
                                             sigvars=sigvars):
            if cnt >= per_prof:
                break
            cnt += 1
            st, lo = le.lp_x(sol, n)
            if st != 'bounded':
                stats['inf'] += 1
                continue
            feas += 1
            stats['feas'] += 1
            deltas[lo] = deltas.get(lo, 0) + 1
            viol = None
            if band != 'low' and lo < F(1, 2):
                viol = 'VIOL-T_low'
            if band == 'high' and lo < 1:
                viol = 'VIOL-T_high'
            if viol:
                stats['violation'].append(
                    dict(d=d, W=str(W), idxs=idxs, lo=str(lo)))
                print('*** %s d=%s W=%s idxs=%s lo=%s'
                      % (viol, d, W, idxs, lo), flush=True)
            if do_gadgets:
                best = le.lg.enumerate_max(sol, n, s)
                bb = None if best is None else best['bound']
                if bb is not None and bb > lo:
                    stats['overcount'].append(
                        dict(d=d, idxs=idxs, lo=str(lo), bb=str(bb)))
                    print('*** OVERCOUNT d=%s lo=%s best=%s'
                          % (d, lo, bb), flush=True)
                if bb is None or bb < lo:
                    stats['undercount'].append(
                        dict(d=d, idxs=idxs, lo=str(lo),
                             bb=None if bb is None else str(bb)))
                    print('*** UNDERCOUNT d=%s lo=%s best=%s'
                          % (d, lo, bb), flush=True)
        mind = min(deltas) if deltas else None
        print('d=%s W=%s band=%s sampled=%d feas=%d deltas=%s '
              '(%.0fs)' % (d, str(W), band, cnt, feas,
                           {str(k): v for k, v in deltas.items()},
                           time.time() - t0), flush=True)
    print('\nSUMMARY feas=%d inf=%d viol=%d over=%d under=%d'
          % (stats['feas'], stats['inf'], len(stats['violation']),
             len(stats['overcount']), len(stats['undercount'])))
    for k in ('violation', 'overcount', 'undercount'):
        for r in stats[k]:
            print(' ', k, r)


if __name__ == '__main__':
    main()
