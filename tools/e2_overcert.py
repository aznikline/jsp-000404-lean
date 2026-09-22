"""Lane E2 — extended-evaluator overcertification hunt.

For each sampled skeleton compute:
  * exact capped / relaxed / free min-delta (Fraction LP), and
  * the extended-evaluator bound (lane_a6.enumerate_max_ext,
    CapKind.low signed caps + vertex floors).

Soundness: a valid gadget proves delta >= bound for EVERY mode-A
point, so  bound > free_min  is an overcertification (soundness
bug).  For consistent skeletons (relaxed_min < 1) also record
bound vs capped_min.

Also tests the lane_a6._CAP_CACHE id(ctx) poisoning hazard: the
cache key is (id(ctx), v, negblk, maxsz); after a Ctx is freed its
id can be reused by the next skeleton's Ctx, returning stale cap
options from a *different* skeleton.  We compare bounds with the
cache warm vs cleared per call.

Usage:
  python3 e2_overcert.py s per_profile workers [seed]
"""
import sys, itertools, time, random, json
sys.path.insert(0, '.')
from fractions import Fraction as F
from multiprocessing import Pool
import lane_e_util as le
import e2_util as e2


def ext_bound(sol, n, s, maxsz=3, clear_cache=True, target=None):
    import lane_a6
    if clear_cache:
        lane_a6._CAP_CACHE.clear()
    return lane_a6.enumerate_max_ext(sol, n, s, maxsz=maxsz,
                                     target=target)


def ext_bound_budgeted(sol, n, s, max_len=3, fan_cap=120, maxsz=4,
                       pivots=None, seed=0):
    """Budgeted extended-enumeration for s>=5 (any produced bound
    must still be sound — undercounting is fine for this hunt)."""
    import lane_a6, link_graph as lg
    rng = random.Random(seed)
    lane_a6._CAP_CACHE.clear()
    ctx = lg.Ctx(sol, n, s)
    best = lg.pure_gadget(ctx)
    if best is not None:
        best = best['bound']
    fas = list(lg.fan_assignments(s))
    if len(fas) > fan_cap:
        fas = [fas[0]] + rng.sample(fas[1:], fan_cap - 1)
    pivots = range(s) if pivots is None else pivots
    for h in pivots:
        outer = [v for v in range(s) if v != h]
        for r_ in range(0, min(max_len, len(outer)) + 1):
            perms = [()] if r_ == 0 else itertools.permutations(
                outer, r_)
            for perm in perms:
                for closed in (False, True):
                    for edges in lg.edge_lists(list(perm), closed):
                        for fa in fas:
                            b = lane_a6.eval_chain_ext(
                                ctx, h, edges, fa, maxsz)
                            if b is not None and (
                                    best is None or b > best):
                                best = b
    return best


def check_one(task):
    s, n, d, sol_data, maxsz = task
    sol = le.data_to_sol(sol_data, n)
    mm = e2.mins_exact(sol, n)
    fmin = mm['free'][1] if mm['free'][0] == 'bounded' else None
    rmin = mm['relaxed'][1] if mm['relaxed'][0] == 'bounded' else None
    # early-exit just above free_min: any return >= target is a
    # definite overcert; returns below it leave a <1/1000 blind spot
    # (documented; flagged cases get a full re-run).
    tgt = fmin + F(1, 1000) if fmin is not None else None
    if s <= 4:
        b = ext_bound(sol, n, s, maxsz=maxsz, target=tgt)
    else:
        b = ext_bound_budgeted(sol, n, s, maxsz=maxsz)
    row = dict(d=list(d), sol=sol_data,
               capped=str(mm['capped'][1]),
               relaxed=str(mm['relaxed'][1]),
               free=str(mm['free'][1]),
               ext=None if b is None else str(b))
    row['consistent'] = bool(rmin is not None and rmin < 1)
    if b is not None and fmin is not None and b > fmin:
        row['OVERCERT'] = dict(bound=str(b), free=str(fmin))
    return row


def sample_sols(s, n, d, per_profile, rng):
    """Sample skeletons (consistent AND capped-infeasible) via
    gen_cases, up to per_profile."""
    ks = le.ks_of_d(n, d)
    try:
        VV = le.ge.build_VV(ks, n, s)
        sigvars = le.ge.build_sigvars(VV, s)
    except Exception:
        return []
    out = []
    for sol, idxs, sk in le.ge.gen_cases(ks, n, s, VV=VV,
                                         sigvars=sigvars):
        out.append(le.sol_to_data(sol))
        if len(out) >= per_profile:
            break
    return out


def poison_test(s, n, d, sol_data):
    """Compare ext bound with warm vs cleared cap cache."""
    import lane_a6
    sol = le.data_to_sol(sol_data, n)
    b_warm = lane_a6.enumerate_max_ext(sol, n, s, maxsz=4)
    lane_a6._CAP_CACHE.clear()
    b_cold = lane_a6.enumerate_max_ext(sol, n, s, maxsz=4)
    return (None if b_warm is None else str(b_warm),
            None if b_cold is None else str(b_cold),
            b_warm != b_cold)


def main():
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    per_prof = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    n = s
    rng = random.Random(seed)
    profs = le.deficit_profiles(n, s)
    tasks = []
    for d in profs:
        W = le.W_of_d(d)
        sols = sample_sols(s, n, d, per_prof, rng)
        for sd in sols:
            tasks.append((s, n, list(d), sd, 4))
    print('skeletons=%d workers=%d' % (len(tasks), workers), flush=True)
    t0 = time.time()
    rows, overs = [], []
    with Pool(workers) as p:
        for i, row in enumerate(p.imap_unordered(check_one, tasks)):
            rows.append(row)
            if row.get('OVERCERT'):
                overs.append(row)
                print('*** OVERCERT d=%s bound=%s free=%s'
                      % (row['d'], row['OVERCERT']['bound'],
                         row['OVERCERT']['free']), flush=True)
            if i % 25 == 0:
                print('  %d/%d (%.0fs)' % (i, len(tasks),
                                           time.time() - t0),
                      flush=True)
            json.dump(rows, open('e2_overcert_s%d.json' % s, 'w'),
                      indent=1)
    print('\ntested=%d overcert=%d (%.0fs)'
          % (len(rows), len(overs), time.time() - t0))


if __name__ == '__main__':
    main()
