"""Lane E — s=6 (and general s) randomized-skeleton level scan.

For each deficit profile in a W window, sample random
edge-consistent skeletons (Sampler), run the FLOAT LP for min-delta,
and confirm every suspicious result with the exact Fraction LP.

Flags:
  VIOL-T_low : 2 < W <= 5/2 band, LP feasible, exact min_delta < 1/2
  VIOL-T_high: W > 5/2, LP feasible, exact min_delta < 1
  NEWLEVEL   : exact min_delta not in {0, 1/2, 1}

Usage:
  python3 e_scan_s6.py s nsamples_per_profile [band] [seed]
    band: all | low(2<W<=5/2) | high(W>5/2) | wle2(W<=2)
"""
import sys, time, random, json
sys.path.insert(0, '.')
from fractions import Fraction as F
import lane_e_util as le


def scan_profile(d, n, s, nsamp, rng):
    ks = le.ks_of_d(n, d)
    smp = le.Sampler(ks, n, s, rng)
    got = 0
    deltas = {}
    worst = []          # lowest-delta feasible skeletons
    attempts = 0
    t0 = time.time()
    while got < nsamp and attempts < 60 * nsamp \
            and time.time() - t0 < 300:
        attempts += 1
        sol = smp.sample()
        if sol is None:
            continue
        got += 1
        st, lo = le.lp_f(sol, n)
        if st != 'bounded':
            deltas['inf'] = deltas.get('inf', 0) + 1
            continue
        # float -> candidate exact value
        lof = F(lo).limit_denominator(96)
        deltas[str(lof)] = deltas.get(str(lof), 0) + 1
        worst.append((lof, le.sol_to_data(sol)))
    return deltas, sorted(worst, key=lambda t: t[0]), attempts


def confirm_exact(sol_data, n):
    sol = le.data_to_sol(sol_data, n)
    return le.lp_x(sol, n)


def main():
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    nsamp = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    band = sys.argv[3] if len(sys.argv) > 3 else 'all'
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    n = s
    rng = random.Random(seed)
    profs = le.deficit_profiles(n, s)
    out = []
    t0 = time.time()
    for d in profs:
        W = le.W_of_d(d)
        if band == 'low' and not (F(2) < W <= F(5, 2)):
            continue
        if band == 'high' and not (W > F(5, 2)):
            continue
        if band == 'wle2' and not (W <= 2):
            continue
        deltas, worst, att = scan_profile(d, n, s, nsamp, rng)
        feas = sum(v for k, v in deltas.items() if k != 'inf')
        # exact-confirm the lowest few
        exact_min = None
        susp = []
        for lof, sdat in worst[:3]:
            stx, lox = confirm_exact(sdat, n)
            if stx == 'bounded':
                exact_min = lox if exact_min is None \
                    else min(exact_min, lox)
                susp.append((str(lox), lof))
        viol = None
        if exact_min is not None:
            if W > F(5, 2) and exact_min < 1:
                viol = 'VIOL-T_high'
            elif W > 2 and exact_min < F(1, 2):
                viol = 'VIOL-T_low'
            elif exact_min not in (F(0), F(1, 2), F(1)):
                viol = 'NEWLEVEL'
        row = dict(d=d, W=str(W), sampled=att, feas=feas,
                   deltas=deltas, exact_min=str(exact_min),
                   viol=viol)
        out.append(row)
        tag = ' *** %s ***' % viol if viol else ''
        print('d=%s W=%s att=%d feas=%d deltas=%s xmin=%s%s'
              % (d, str(W), att, feas, deltas,
                 str(exact_min), tag), flush=True)
        if viol:
            fx = dict(d=list(d), W=str(W), exact_min=str(exact_min),
                      sol=worst[0][1])
            json.dump(fx, open('lane_e_cex_%s_%s.json'
                               % (viol, ''.join(map(str, d))), 'w'),
                      indent=1)
    json.dump(out, open('lane_e_scan_s%d_%s.json' % (s, band), 'w'),
              indent=1)
    nv = sum(1 for r in out if r['viol'])
    print('\nprofiles=%d violations=%d (%.0fs)'
          % (len(out), nv, time.time() - t0))


if __name__ == '__main__':
    main()
