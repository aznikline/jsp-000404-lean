"""Parallel scan: for a profile, check every skeleton for a level-1
gadget (staged: fan -> 1-link -> 2-link -> full), and for failures
run extended-cap eval + LP status.  Reports counts."""
import sys, json, itertools, time, os
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import generic_model as gm
import link_graph as lg
import residual_map as rm
from lane_a6 import eval_chain_ext

HALF = F(1, 2)
GKS = None
GVV = None
GSIG = None
GN = GS = 0


def worker_init(ks, n, s):
    global GKS, GVV, GSIG, GN, GS
    GKS, GN, GS = ks, n, s
    GVV = ge.build_VV(ks, n, s)
    GSIG = ge.build_sigvars(GVV, s)


def compact(sol):
    return [(tuple(v['order']),
             tuple(v['bits'][x] for x in v['order']),
             tuple(v['qs'])) for v in sol]


def expand(cs, n, s):
    """Rebuild Ctx-facing dicts: order, bits (dict), qs."""
    sol = []
    for v in range(s):
        order, btup, qs = cs[v]
        bits = {x: b for x, b in zip(order, btup)}
        sol.append({'order': order, 'bits': bits, 'qs': qs})
    return sol


def stage_search(ctx, n, s):
    """Return (stage, bound) of first gadget reaching >=1/2."""
    fas = list(lg.fan_assignments(s))
    best = None
    pg = lg.pure_gadget(ctx)
    if pg is not None:
        best = pg['bound']
        if best >= HALF:
            return 0, best
    for fa in fas:
        b = lg.eval_chain(ctx, 0, [], fa)
        if b is not None:
            if best is None or b['bound'] > best:
                best = b['bound']
            if b['bound'] >= HALF:
                return 1, b['bound']
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        for a, b_ in itertools.combinations(outer, 2):
            for sig in (1, -1):
                edges = [(a, b_, sig)]
                for fa in fas:
                    r = lg.eval_chain(ctx, h, edges, fa)
                    if r is not None:
                        if best is None or r['bound'] > best:
                            best = r['bound']
                        if r['bound'] >= HALF:
                            return 3, r['bound']
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        for a, b_, c_ in itertools.permutations(outer, 3):
            for s1, s2 in itertools.product((1, -1), repeat=2):
                edges = [(a, b_, s1), (b_, c_, s2)]
                for fa in fas:
                    r = lg.eval_chain(ctx, h, edges, fa)
                    if r is not None:
                        if best is None or r['bound'] > best:
                            best = r['bound']
                        if r['bound'] >= HALF:
                            return 4, r['bound']
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        if len(outer) == 3:
            a, b_, c_ = outer
            for sg in itertools.product((1, -1), repeat=3):
                edges = [(a, b_, sg[0]), (b_, c_, sg[1]), (c_, a, sg[2])]
                for fa in fas:
                    r = lg.eval_chain(ctx, h, edges, fa)
                    if r is not None:
                        if best is None or r['bound'] > best:
                            best = r['bound']
                        if r['bound'] >= HALF:
                            return 5, r['bound']
    return 6, best


def process(item):
    """item: (idxs, compact skeleton). Returns status tuple."""
    idxs, cs = item
    sol = expand(cs, GN, GS)
    ctx = lg.Ctx(sol, GN, GS)
    st, bound = stage_search(ctx, GN, GS)
    if bound is not None and bound >= HALF:
        return ('ok', st, None)
    # no standard L1 gadget: try extended caps on same shapes
    bext = None
    for h in range(GS):
        outer = [v for v in range(GS) if v != h]
        for r_ in range(0, 4):
            perms = [()] if r_ == 0 else itertools.permutations(outer, r_)
            for perm in perms:
                for closed in (False, True):
                    for edges in lg.edge_lists(list(perm), closed):
                        for fa in lg.fan_assignments(GS):
                            b = eval_chain_ext(ctx, h, edges, fa)
                            if b is not None and (
                                    bext is None or b > bext):
                                bext = b
    if bext is not None and bext >= HALF:
        return ('ext_ok', 7, str(bext))
    # LP status
    VV = GVV
    sol_full = [VV[v][idxs[v]] for v in range(GS)]
    E = rm.load_g()
    st_, lo = lg.lp_level(E, sol_full, GN)
    return ('FAIL', None,
            (str(bext), st_, str(lo), idxs))


def gen_items(ks, n, s):
    VV = ge.build_VV(ks, n, s)
    sigvars = ge.build_sigvars(VV, s)
    for sol, idxs, sigk in ge.gen_cases(ks, n, s, VV=VV, sigvars=sigvars):
        yield (idxs, compact(sol))


def main():
    n = s = 4
    ks = json.loads(sys.argv[1])
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    stride = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    from multiprocessing import Pool
    t0 = time.time()
    cnt = 0
    stats = {}
    fails = []
    items = []
    for i, it in enumerate(gen_items(ks, n, s)):
        if stride > 1 and i % stride:
            continue
        items.append(it)
        cnt += 1
        if limit and cnt >= limit:
            break
    print(f'enumerated {cnt}', flush=True)
    with Pool(8, initializer=worker_init, initargs=(ks, n, s)) as pool:
        for res in pool.imap_unordered(process, items, chunksize=64):
            tag = res[0]
            stats[tag] = stats.get(tag, 0) + 1
            if tag == 'FAIL':
                fails.append(res[2])
                if len(fails) <= 20:
                    print('FAIL', res[2], flush=True)
    print(f'sampled={cnt} stats={stats} fails={len(fails)} '
          f'({time.time()-t0:.0f}s)', flush=True)


if __name__ == '__main__':
    main()
