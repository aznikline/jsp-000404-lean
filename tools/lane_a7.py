"""Broad validation of the extended-cap gadget evaluator.

For each W>2 profile (s=4,n=4) sample skeletons, compute:
  LP delta_min status  in {0, 1/2, 1, inf}
  extended gadget bound
Check: every skeleton has ext bound >= LP bound (gadget-complete at
the level boundary), in particular every W>2 skeleton admits a
gadget with bound >= 1/2 -- including 'inf' (infeasible) ones.
"""
import sys, itertools, time
sys.path.insert(0, '.')
from fractions import Fraction as F
from multiprocessing import Pool
import generic_enum as ge, generic_model as gm, residual_map as rm
from lane_a6 import enumerate_max_ext

N = S = 4
E = rm.load_g()


def worker(arg):
    ks, idxs, sol = arg
    gm.ORIG.clear()
    ineqs, eqs = gm.build_case(sol, N, 'A')
    ineqs = gm.substitute(eqs, ineqs)
    st, lo, y = rm.glp_min_delta(ineqs, E.CONST, E.DELTA)
    lp = None if st != 'bounded' else lo
    lpstat = 'inf' if st == 'infeasible' else lp
    b = enumerate_max_ext(sol, N, S)
    return ks, idxs, lpstat, b


def W_of(ks):
    return sum(F(2) ** (k - (N - 1)) for k in ks)


def profiles():
    out = []
    for ks in itertools.combinations_with_replacement(
            range(N), S):
        if len(ks) == S and W_of(ks) > 2:
            out.append(tuple(sorted(ks, reverse=True)))
    return sorted(set(out))


def main():
    per = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    jobs = []
    for ks in profiles():
        VV = ge.build_VV(list(ks), N, S)
        sigvars = ge.build_sigvars(VV, S)
        cnt = 0
        for sol, idxs, sigk in ge.gen_cases(list(ks), N, S,
                                          VV=VV, sigvars=sigvars):
            jobs.append((list(ks), idxs, [dict(x) for x in sol]))
            cnt += 1
            if cnt >= per:
                break
    print(f'{len(jobs)} jobs over {len(profiles())} profiles',
          flush=True)
    stats = {}
    fails = []
    t0 = time.time()
    with Pool(8) as P:
        for i, (ks, idxs, lp, b) in enumerate(
                P.imap_unordered(worker, jobs)):
            key = (str(lp), )
            stats[key] = stats.get(key, 0) + 1
            need = F(1, 2)
            ok = (b is not None and b >= need)
            if lp == 'inf' or (lp is not None and lp >= 1):
                # phantom / inconsistent: bonus coverage
                ok = ok and (b >= 1)
            if not ok:
                fails.append((ks, idxs, lp, b))
            if (i + 1) % 100 == 0:
                print(f'{i+1}/{len(jobs)} {time.time()-t0:.0f}s '
                      f'fails={len(fails)}', flush=True)
    print('stats:', stats)
    print('FAILS:', len(fails))
    for f in fails[:30]:
        print('  ', f)


if __name__ == '__main__':
    main()
