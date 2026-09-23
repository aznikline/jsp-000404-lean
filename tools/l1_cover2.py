"""Lane L1 — staged coverage scan.

Stage A: LINK-only bound on every consistent W>2 skeleton (cheap).
Stage B: on LINK-uncovered, FANLINK with a bounded grammar
         (<=2 links sharing a pivot, <=1 fan weight +-1) — B3's
         STRIP-A/B shape — recording the minimal witness.
Stage C (reported separately): PURE/FAN0/FANALL bounds, to confirm
         fan-only gadgets never suffice.

Usage: python3 l1_cover2.py s n d max_sols workers
"""
import sys, itertools, time, json
sys.path.insert(0, '.')
from fractions import Fraction as F
from multiprocessing import Pool
import lane_e_util as le
import e2_util as e2
import link_graph as lg
import lane_a6
from l1_cover import eval_ctx, pure_bound, single_fan_bound, \
    all_fan_bound, gen_consistent

ZERO = F(0)
HALF = F(1, 2)


def link_sets(s, max_links=3):
    """All (h, edges) where edges is a list (a,b,sig) on a path or
    closed cycle through pivot h."""
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        for r_ in range(1, min(max_links + 1, len(outer) + 1)):
            for perm in itertools.permutations(outer, r_):
                for closed in (False, True):
                    for el in lg.edge_lists(list(perm), closed):
                        yield h, el


def link_bound_wit(ctx, maxsz=5):
    best = None
    wit = None
    for h, el in link_sets(ctx.s):
        edges = [(a, b, sg, h) for a, b, sg in el]
        b = eval_ctx(ctx, edges, {}, maxsz)
        if b is not None and (best is None or b > best):
            best, wit = b, ('LINK', h, el)
    return best, wit


def fanlink_bound_wit(ctx, maxsz=5, max_links=2):
    """<=1 fan (+-1) + <=max_links signed links on one pivot."""
    s = ctx.s
    best = None
    wit = None
    for h, el in link_sets(s, max_links):
        edges = [(a, b, sg, h) for a, b, sg in el]
        for v in range(s):
            for w in (1, -1):
                b = eval_ctx(ctx, edges, {v: w}, maxsz)
                if b is not None and (best is None or b > best):
                    best, wit = b, ('FANLINK', h, el, v, w)
    return best, wit


def fanlink2_bound_wit(ctx, maxsz=5, max_links=2, max_fans=3):
    """<=max_fans fans + <=max_links links — the full STRIP grammar."""
    s = ctx.s
    fas = []
    for tup in itertools.product((-1, 0, 1), repeat=s):
        fa = {v: t for v, t in enumerate(tup) if t}
        if 2 <= len(fa) <= max_fans:
            fas.append(fa)
    best = None
    wit = None
    for h, el in link_sets(s, max_links):
        edges = [(a, b, sg, h) for a, b, sg in el]
        for fa in fas:
            b = eval_ctx(ctx, edges, fa, maxsz)
            if b is not None and (best is None or b > best):
                best, wit = b, ('FANLINK2', h, el, fa)
    return best, wit


def work(task):
    i, s, n, d, sol_data = task
    sol = le.data_to_sol(sol_data, n)
    lane_a6._CAP_CACHE.clear()
    ctx = lg.Ctx(sol, n, s)
    lb, lwit = link_bound_wit(ctx)
    row = dict(i=i, d=list(d), sol=sol_data,
               link=(str(lb) if lb is not None else None),
               linkwit=(lwit if lb is not None and lb >= HALF
                        else None))
    if lb is None or lb < HALF:
        fb, fwit = fanlink_bound_wit(ctx)
        row['fl'] = str(fb) if fb is not None else None
        row['flwit'] = fwit if fb is not None and fb >= HALF else None
        if fb is None or fb < HALF:
            f2, f2wit = fanlink2_bound_wit(ctx)
            row['fl2'] = str(f2) if f2 is not None else None
            row['fl2wit'] = (f2wit if f2 is not None
                             and f2 >= HALF else None)
    return row


def main():
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    n = int(sys.argv[2]) if len(sys.argv) > 2 else s
    profs = sys.argv[3] if len(sys.argv) > 3 else 'all'
    max_sols = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 9
    workers = int(sys.argv[5]) if len(sys.argv) > 5 else 8
    if profs == 'all':
        ds = [d for d in le.deficit_profiles(n, s)
              if le.W_of_d(d) > 2]
    else:
        ds = [tuple(int(x) for x in profs.split(','))]
    tasks = []
    for d in ds:
        sols, st = gen_consistent(s, n, d, max_sols)
        print('profile %s: %d consistent skeletons' % (d, len(sols)),
              flush=True)
        for i, sd in enumerate(sols):
            tasks.append((len(tasks), s, n, d, sd))
    print('total tasks=%d workers=%d' % (len(tasks), workers),
          flush=True)
    t0 = time.time()
    tally = {}
    flwit_tally = {}
    uncovered = []
    done = 0
    with Pool(workers) as p:
        for row in p.imap_unordered(work, tasks, chunksize=4):
            done += 1
            if row.get('linkwit') is not None:
                key = 'LINK'
            elif row.get('flwit') is not None:
                key = 'FANLINK(1fan,<=2links)'
                w = row['flwit']
                flwit_tally[(w[1], len(w[2]), w[3], w[4])] = \
                    flwit_tally.get(
                        (w[1], len(w[2]), w[3], w[4]), 0) + 1
            elif row.get('fl2wit') is not None:
                key = 'FANLINK2'
            else:
                key = 'UNCOVERED'
                uncovered.append(row)
            tally[key] = tally.get(key, 0) + 1
            if done % 500 == 0:
                print('  %d/%d (%.0fs) tally=%s'
                      % (done, len(tasks), time.time() - t0, tally),
                      flush=True)
    print('\nSTAGE tally:', tally)
    print('FANLINK witness shapes (h,#links,v,w):', flwit_tally)
    print('uncovered=%d (%.0fs)' % (len(uncovered), time.time() - t0))
    json.dump(dict(tally=tally,
                   uncovered=uncovered[:30],
                   total=done),
              open('l1_cover2_s%dn%d.json' % (s, n), 'w'), indent=1)


if __name__ == '__main__':
    main()
