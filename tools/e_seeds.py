"""Lane E — harvest feasible geometric skeletons into a
profile->seeds library for the profile-preserving climber.

Usage: python3 e_seeds.py s nconf [seed] [n]
Writes lane_e_seeds_s{S}n{N}.json : {d_str: [sol_data,...]}
"""
import sys, math, random, time, json
sys.path.insert(0, '.')
from fractions import Fraction as F
import lane_e_util as le
from e_geom import real_skel, gen_config


def data_of(sol):
    return [{'order': list(sol[v]['order']),
             'bits': {str(k): b for k, b in sol[v]['bits'].items()},
             'qs': list(sol[v]['qs'])} for v in range(len(sol))]


def main():
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    nconf = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    n = int(sys.argv[4]) if len(sys.argv) > 4 else s
    rng = random.Random(seed)
    fams = ['collinear', 'collinear2', 'circle', 'cluster',
            'twoarc', 'random']
    seeds = {}
    feas = 0
    t0 = time.time()
    for tr in range(nconf):
        fam = fams[tr % len(fams)]
        for dval in (0.05, 0.2, 0.35, 0.5, 0.65, 0.8, 0.95):
            lam = 1.0 / (n + dval)
            out = real_skel(gen_config(fam, s, rng), n, lam)
            if out is None:
                continue
            sol, kv = out
            if any(k >= n for k in kv):
                continue          # 'top' hypothesis: k < n
            st, lo = le.lp_f(sol, n)
            if st != 'bounded':
                continue
            feas += 1
            d = tuple(sorted(n - 1 - k for k in kv))
            seeds.setdefault(str(d), [])
            if len(seeds[str(d)]) < 6:
                seeds[str(d)].append(
                    dict(data=data_of(sol), mind=float(lo)))
    json.dump(seeds,
              open('lane_e_seeds_s%dn%d.json' % (s, n), 'w'),
              indent=1)
    print('feasible=%d profiles=%d (%.0fs)'
          % (feas, len(seeds), time.time() - t0))
    hi = [d for d in seeds
          if le.W_of_d(tuple(map(int, d[1:-1].split(', ')))) > F(5, 2)]
    mid = [d for d in seeds
           if F(2) < le.W_of_d(
               tuple(map(int, d[1:-1].split(', ')))) <= F(5, 2)]
    print('high-band profiles seeded: %d' % len(hi))
    for d in sorted(hi, key=lambda x: -float(le.W_of_d(
            tuple(map(int, x[1:-1].split(', ')))))):
        print('   ', d)
    print('mid-band profiles seeded: %d' % len(mid))
    for d in sorted(mid):
        print('   ', d)


if __name__ == '__main__':
    main()
