"""Lane E2 — parallel profile campaign (s-generic).

Per profile d (W > 2):
  pass 1 'feas': guided DFS collecting consistent skeletons
         (relaxed float min < 1); each leaf screened by float
         free-min; flagged leaves exact-verified.
  pass 2 'cex' : guided DFS pruned to free-min < thr
         (thr = 1 for W > 5/2 -> T_high hunt; 1/2 for mid band ->
         T_low hunt); every leaf is a counterexample candidate,
         exact-verified immediately.

Kill criteria (exact):
  consistent (relaxed_min < 1) AND
    (W > 5/2 AND free_min < 1)      -> T_high counterexample
    (W > 2   AND free_min < 1/2)    -> T_low counterexample

Usage:
  python3 e2_campaign.py s n band workers feas_secs cex_secs
    band: hi | mid | all   workers: pool size
Writes e2_campaign_s{S}n{N}_{band}.json + prints progress.
"""
import sys, os, json, time, random
sys.path.insert(0, '.')
from fractions import Fraction as F
from multiprocessing import Pool
import lane_e_util as le
import e2_util as e2

FLOAT_MARGIN = 1e-6


def float_mins(sol_data, n, s):
    sol = le.data_to_sol(sol_data, n)
    out = {}
    for mode in ('relaxed', 'free'):
        nv, cons, obj = e2.float_cons(sol, list(range(s)), s, n, mode)
        out[mode] = e2.lp_min_f(nv, cons, obj)
    return out


def run_profile(task):
    s, n, d, feas_secs, cex_secs, max_sols, seed = task
    rng = random.Random(seed)
    d = tuple(d)
    W = le.W_of_d(d)
    ks = le.ks_of_d(n, d)
    hi = W > F(5, 2)
    thr = 1.0 if hi else 0.5
    row = dict(d=list(d), W=str(W), band='hi' if hi else 'mid')
    flagged = []
    viol = []

    # ---------------- pass 1: feas ----------------
    t0 = time.time()
    leaves = 0
    cons_leaves = 0
    free_lo = None
    stats1 = {}
    gen = e2.guided(ks, n, s, mode='feas', max_sols=max_sols,
                    deadline=feas_secs, rng=rng)
    for sdat, st in gen:
        if sdat is None:
            stats1 = st
            break
        leaves += 1
        fm = float_mins(sdat, n, s)
        rs, rmin = fm['relaxed']
        fs, fmin = fm['free']
        if rs != 'bounded' or rmin >= 1 - FLOAT_MARGIN:
            continue
        cons_leaves += 1
        if fs == 'bounded':
            if free_lo is None or fmin < free_lo:
                free_lo = fmin
            if fmin < thr - FLOAT_MARGIN:
                v = e2.verify_candidate(sdat, n, s, d)
                if v['viol']:
                    viol.append(dict(v, sol=sdat))
                else:
                    flagged.append(dict(
                        float_free=fmin, exact=v, sol=sdat))
    row['feas'] = dict(leaves=leaves, consistent=cons_leaves,
                       free_min_float=free_lo, stats=stats1,
                       secs=round(time.time() - t0, 1))

    # ---------------- pass 2: cex ----------------
    t0 = time.time()
    cleaves = 0
    stats2 = {}
    gen = e2.guided(ks, n, s, mode='cex', free_thr=thr,
                    max_sols=max_sols, deadline=cex_secs, rng=rng)
    for sdat, st in gen:
        if sdat is None:
            stats2 = st
            break
        cleaves += 1
        v = e2.verify_candidate(sdat, n, s, d)
        if v['viol']:
            viol.append(dict(v, sol=sdat))
        else:
            flagged.append(dict(cex_leaf=True, exact=v, sol=sdat))
    row['cex'] = dict(leaves=cleaves, thr=thr, stats=stats2,
                      secs=round(time.time() - t0, 1))
    row['flagged'] = flagged[:5]
    row['n_flagged'] = len(flagged)
    row['viol'] = viol
    return row


def main():
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    n = int(sys.argv[2]) if len(sys.argv) > 2 else s
    band = sys.argv[3] if len(sys.argv) > 3 else 'all'
    workers = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    feas_secs = float(sys.argv[5]) if len(sys.argv) > 5 else 30
    cex_secs = float(sys.argv[6]) if len(sys.argv) > 6 else 45
    max_sols = int(sys.argv[7]) if len(sys.argv) > 7 else 20
    profs = le.deficit_profiles(n, s)
    tasks = []
    for i, d in enumerate(profs):
        W = le.W_of_d(d)
        if band == 'hi' and not W > F(5, 2):
            continue
        if band == 'mid' and not (F(2) < W <= F(5, 2)):
            continue
        if band == 'all' and not W > 2:
            continue
        tasks.append((s, n, list(d), feas_secs, cex_secs, max_sols,
                      1000 + i))
    print('profiles=%d workers=%d feas=%ss cex=%ss'
          % (len(tasks), workers, feas_secs, cex_secs), flush=True)
    t0 = time.time()
    out = []
    nviol = 0
    with Pool(workers) as p:
        for row in p.imap_unordered(run_profile, tasks):
            out.append(row)
            fv = row['feas']
            cv = row['cex']
            tag = ''
            if row['viol']:
                nviol += 1
                tag = '  *** VIOLATION ***'
            elif row['n_flagged']:
                tag = '  (flagged %d)' % row['n_flagged']
            print('d=%s W=%s feas[leaves=%d cons=%d flo=%s %.0fs] '
                  'cex[leaves=%d %.0fs]%s'
                  % (row['d'], row['W'], fv['leaves'],
                     fv['consistent'], fv['free_min_float'],
                     fv['secs'], cv['leaves'], cv['secs'], tag),
                  flush=True)
            json.dump(out, open(
                'e2_campaign_s%dn%d_%s.json' % (s, n, band), 'w'),
                indent=1, default=str)
    print('\ndone %d profiles, %d violations (%.0fs)'
          % (len(out), nviol, time.time() - t0))


if __name__ == '__main__':
    main()
