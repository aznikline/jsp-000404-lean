"""Lane L1 (wave 3) — branch-coverage scan for GadgetSelectionLowP.

Replicates the B3 methodology for the LOW regime: define a branch
taxonomy of level-1 gadget families (bound >= 1/2), enumerate ALL
consistent W>2 skeletons at s=4 via LP-pruned guided DFS (sound:
partial relaxed-min >= 1 prunes subtrees with no consistent leaf),
and record which branch families certify each skeleton.

Branch grammar (ordered, B3-style):

  PURE    : caps only — no fans, no links.  Includes direct-arc caps
            (q_arc >= n) and vertex floors (signed low caps on empty
            negative blocks).  bound = -Bcap / uu.
  FAN0    : exactly one signed fan (w = +-1), no links, + charges and
            generalized caps (incl. floors on other vertices).
  LINK    : signed links only (open path or closed cycle on one
            pivot h), no fans, + charges/caps.
  FANLINK : fans and links both present (minimal count recorded).

For coverage we only need ONE certificate per skeleton: branches are
tried cheap-first with early exit at bound >= 1/2.  When a skeleton
is certified by several families we record the FIRST hit plus, in a
second pass, the full family hit-set (to know whether e.g. FAN0 alone
would suffice).

Usage:
  python3 l1_cover.py s n d_tuple max_sols [sample_every]
"""
import sys, itertools, time, json
sys.path.insert(0, '.')
from fractions import Fraction as F
from multiprocessing import Pool
import lane_e_util as le
import e2_util as e2
import link_graph as lg
import lane_a6

ZERO = F(0)
HALF = F(1, 2)


# ---------------------------------------------------------------------
# family-stratified evaluation: same residual machinery as lane_a6 but
# returns (best_bound, witness) so we can classify the certificate.
# ---------------------------------------------------------------------

def eval_ctx(ctx, edges, fans, maxsz=5):
    """lane_a6.eval_chain_ext minus the pivot arg (link dicts are
    keyed on the pivot inside ctx.link)."""
    n, s = ctx.n, ctx.s
    R = {}
    con = ZERO
    dc = 0
    for v, fw in fans.items():
        Rd, cc, dd = ctx.fan[(v, fw)]
        for k, t in Rd.items():
            R[k] = R.get(k, 0) + t
        con += cc
        dc += dd
    for a, b, sig, h in edges:
        Rd, cc, dd = ctx.link[(min(a, b), max(a, b), h, sig)]
        for k, t in Rd.items():
            R[k] = R.get(k, 0) + t
        con += cc
        dc += dd
    c = -dc
    C = -con
    K = ZERO
    cap_vars = []
    for v in range(s):
        blk = {g: R.get((v, g), 0) for g in range(s - 1)}
        blk = {g: k for g, k in blk.items() if k != 0}
        posblk = {g: k for g, k in blk.items() if k > 0}
        negblk = {g: -k for g, k in blk.items() if k < 0}
        if posblk:
            pset = frozenset(posblk)
            cand = []
            for rng, q in ctx.comp_ang[v]:
                if rng <= pset:
                    gain = min(posblk[g] for g in rng) * (F(1) - q)
                    if gain > 0:
                        cand.append((gain, rng))
            cand.sort(key=lambda t: -t[0])
            used = frozenset()
            for gain, rng in cand:
                if not (rng & used):
                    K += gain
                    used |= rng
        if negblk:
            cap_vars.append(lane_a6.cap_options_ext(ctx, v, negblk,
                                                    maxsz))
        else:
            floor_opts = [(ZERO, ZERO)] + [
                o for o in lane_a6.cap_options_ext(ctx, v, {}, maxsz)
                if o[0] < 0]
            if len(floor_opts) > 1:
                cap_vars.append(floor_opts)
    c = F(c)
    best = None
    for combo in itertools.product(*cap_vars) if cap_vars else [()]:
        Bcap = sum(t[0] for t in combo)
        u = sum(t[1] for t in combo)
        if c + u <= 0:
            continue
        bound = (K - Bcap - C) / (c + u)
        if best is None or bound > best:
            best = bound
    return best


def pure_bound(ctx, maxsz=5):
    """Caps-only gadget bound (no equalities): B3's PURE + floors."""
    return eval_ctx(ctx, [], {}, maxsz)


def single_fan_bound(ctx, maxsz=5):
    """Best bound over gadgets with exactly one fan weight, no links."""
    s = ctx.s
    best = None
    for v in range(s):
        for w in (1, -1):
            b = eval_ctx(ctx, [], {v: w}, maxsz)
            if b is not None and (best is None or b > best):
                best = b
    return best


def all_fan_bound(ctx, maxsz=5):
    """Best bound over fan-only gadgets (any fan assignment)."""
    s = ctx.s
    best = None
    for tup in itertools.product((-1, 0, 1), repeat=s):
        fa = {v: t for v, t in enumerate(tup) if t}
        if len(fa) <= 1:
            continue
        b = eval_ctx(ctx, [], fa, maxsz)
        if b is not None and (best is None or b > best):
            best = b
    return best


def link_bound(ctx, maxsz=5, max_links=3):
    """Best bound over link-only gadgets: open paths and closed
    cycles through a pivot h (B3's STRIP grammar)."""
    s = ctx.s
    best = None
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        for r_ in range(1, min(max_links + 1, len(outer) + 1)):
            for perm in itertools.permutations(outer, r_):
                for closed in (False, True):
                    for el in lg.edge_lists(list(perm), closed):
                        edges = [(a, b, sg, h) for a, b, sg in el]
                        b = eval_ctx(ctx, edges, {}, maxsz)
                        if b is not None and (best is None or b > best):
                            best = b
    return best


def fanlink_bound(ctx, maxsz=5, max_links=3, max_fans=2):
    """Best bound over gadgets with >=1 fan AND >=1 link
    (bounded fan support for tractability)."""
    s = ctx.s
    fas = []
    for tup in itertools.product((-1, 0, 1), repeat=s):
        fa = {v: t for v, t in enumerate(tup) if t}
        if 1 <= len(fa) <= max_fans:
            fas.append(fa)
    best = None
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        for r_ in range(1, min(max_links + 1, len(outer) + 1)):
            for perm in itertools.permutations(outer, r_):
                for closed in (False, True):
                    for el in lg.edge_lists(list(perm), closed):
                        edges = [(a, b, sg, h) for a, b, sg in el]
                        for fa in fas:
                            b = eval_ctx(ctx, edges, fa, maxsz)
                            if (b is not None
                                    and (best is None or b > best)):
                                best = b
    return best


# ---------------------------------------------------------------------
# per-skeleton classification
# ---------------------------------------------------------------------

def classify(sol, n, s, budget='full'):
    """Return dict of per-branch best bounds (None = family gives
    no valid gadget)."""
    lane_a6._CAP_CACHE.clear()
    ctx = lg.Ctx(sol, n, s)
    out = {}
    out['PURE'] = pure_bound(ctx)
    out['FAN0'] = single_fan_bound(ctx)
    out['FANALL'] = all_fan_bound(ctx)
    out['LINK'] = link_bound(ctx)
    if budget == 'full':
        out['FANLINK'] = fanlink_bound(ctx)
    return out


def first_hit(bounds):
    for fam in ('PURE', 'FAN0', 'FANALL', 'LINK', 'FANLINK'):
        b = bounds.get(fam)
        if b is not None and b >= HALF:
            return fam
    return None


def hit_set(bounds):
    return [fam for fam in ('PURE', 'FAN0', 'FANALL', 'LINK',
                            'FANLINK')
            if bounds.get(fam) is not None and bounds[fam] >= HALF]


def work(task):
    i, s, n, d, sol_data = task
    sol = le.data_to_sol(sol_data, n)
    bounds = classify(sol, n, s)
    return dict(i=i, d=list(d), sol=sol_data,
                bounds={k: (str(v) if v is not None else None)
                        for k, v in bounds.items()},
                first=first_hit(bounds),
                hits=hit_set(bounds))


def gen_consistent(s, n, d, max_sols):
    ks = le.ks_of_d(n, d)
    out = []
    for sol_data, st in e2.guided(ks, n, s, mode='feas',
                                  max_sols=max_sols):
        if sol_data is None:
            return out, st
        out.append(sol_data)
    return out, None


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
    rows = []
    tally = {}
    hits_tally = {}
    uncovered = []
    with Pool(workers) as p:
        for row in p.imap_unordered(work, tasks, chunksize=4):
            rows.append(row)
            f = row['first'] or 'UNCOVERED'
            tally[f] = tally.get(f, 0) + 1
            hs = '+'.join(row['hits']) or 'none'
            hits_tally[hs] = hits_tally.get(hs, 0) + 1
            if row['first'] is None:
                uncovered.append(row)
            if len(rows) % 500 == 0:
                print('  %d/%d (%.0fs) tally=%s'
                      % (len(rows), len(tasks), time.time() - t0,
                         tally), flush=True)
    print('\nFIRST-HIT tally:', tally)
    print('HIT-SET tally:', hits_tally)
    print('uncovered=%d (%.0fs)' % (len(uncovered), time.time() - t0))
    tag = 's%dn%d' % (s, n)
    json.dump(dict(tally=tally, hits=hits_tally,
                   uncovered=uncovered[:50], rows=len(rows)),
              open('l1_cover_%s.json' % tag, 'w'), indent=1)


if __name__ == '__main__':
    main()
