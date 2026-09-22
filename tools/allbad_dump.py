"""All-bad strip analysis (Lane B3, JSP-000404).

Enumerate mode-A-consistent skeletons of W>5/2 profiles at s=n=4
where >=2 vertices are saturated AND every saturated vertex is bad
(no local delta>=1 gadget: bit threshold sits exactly at the heavy
gap).  For each such skeleton dump:

  * per-vertex mode/order/bits/qs,
  * for every bad pair (i,j): slot of j in i's fan relative to i's
    heavy gap (L = before-gap endpoint, R = after-gap endpoint,
    O = opposite), and both edge-side signatures,
  * the winning certificate (block / pure / fan+links strip) with
    the charge vertex and cap vertices identified.

Aggregate: which (mode_i, slot_i | mode_j, slot_j) pairs occur, and
whether a uniform charge/cap pattern exists.

Usage: python3 allbad_dump.py [d0 d1 d2 d3 ...] [--max N] [--json]
"""
import sys, json, itertools, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import generic_model as gm
import seidel_lp
import link_graph as lg
import eval_ext as ex

N = S = 4
CONST, DELTA = gm.CONST, gm.DELTA

PROFILES = {
    (0, 0, 0, 0): (3, 3, 3, 3),
    (0, 0, 0, 1): (3, 3, 3, 2),
    (0, 0, 0, 2): (3, 3, 3, 1),
    (0, 0, 0, 3): (3, 3, 3, 0),
    (0, 0, 1, 1): (3, 3, 2, 2),
    (0, 0, 1, 2): (3, 3, 2, 1),
    (0, 0, 1, 3): (3, 3, 2, 0),
}


# ---------- feasibility (unclamped-delta mode A = SkeletonConsistent)

def lp_feas_unclamped(sol, cap=1000.0):
    """Unclamped-delta feasibility: drop the 'δ<1' row and let δ range
    up to `cap`.  Returns (status, min_delta|None)."""
    gm.ORIG.clear()
    ineqs, eqs = gm.build_case(sol, N, 'A', skip={'δ<1'})
    ineqs = gm.substitute(eqs, ineqs)
    present = sorted({v for q in ineqs for v in q.a if v != CONST},
                     key=str)
    if DELTA not in present:
        present.append(DELTA)
    idx = {v: t for t, v in enumerate(present)}
    nv = len(present)
    cons = [([float(q.a.get(v, 0)) for v in present],
             float(q.b) - float(q.a.get(CONST, 0)))
            for q in ineqs]
    obj = [0.0] * nv
    obj[idx[DELTA]] = -1.0
    bounds = [(0.0, 1.0)] * nv
    bounds[idx[DELTA]] = (0.0, cap)
    r = seidel_lp.lp_max(nv, cons, obj, bounds)
    if r[0] == 'infeasible':
        return ('infeasible', None)
    return ('bounded', -r[1])


# ---------- saturated-vertex classification

def heavy_pos(ctx, v):
    qs = ctx.qs_b[v] if isinstance(ctx, lg.Ctx) else ctx[v]['qs']
    hs = [g for g, q in enumerate(qs) if q == N]
    if len(hs) == 1 and all(q == 0 for g, q in enumerate(qs)
                            if g != hs[0]):
        return hs[0]
    return None


def _bits_pos(ctx, v):
    if isinstance(ctx, lg.Ctx):
        return ctx.bits_b[v], ctx.pos_b[v]
    vv = ctx[v]
    return vv['bits'], {d: t for t, d in enumerate(vv['order'])}


def is_bad(ctx, v):
    """saturated with no local gadget (bit threshold at heavy gap)."""
    hp = heavy_pos(ctx, v)
    if hp is None:
        return False
    bits, pos = _bits_pos(ctx, v)
    others = [t for t in range(S) if t != v]
    for a, b in itertools.combinations(others, 2):
        lo, hi = sorted((pos[a], pos[b]))
        has_heavy = lo <= hp < hi
        if bits[a] == bits[b] and has_heavy:
            return False
        if bits[a] != bits[b] and not has_heavy:
            return False
    return True


def vv_is_bad(vv):
    """badness of a single variant dict (label-agnostic)."""
    hp = heavy_pos([vv], 0)
    if hp is None:
        return False
    bits = vv['bits']
    pos = {d: t for t, d in enumerate(vv['order'])}
    for a, b in itertools.combinations(list(vv['order']), 2):
        lo, hi = sorted((pos[a], pos[b]))
        has_heavy = lo <= hp < hi
        if bits[a] == bits[b] and has_heavy:
            return False
        if bits[a] != bits[b] and not has_heavy:
            return False
    return True


def fmode(ctx, v):
    """'F1'|'F2'|'F3' for a bad vertex (heavy gap position)."""
    return 'F' + str(heavy_pos(ctx, v) + 1)


def slot(ctx, i, j):
    """Where j sits in bad vertex i's fan relative to i's heavy gap.
    'L' = direction before the heavy gap (pos == hp),
    'R' = direction after it (pos == (hp+1) % 3),
    'O' = the remaining (opposite) direction."""
    hp = heavy_pos(ctx, i)
    _, pos = _bits_pos(ctx, i)
    pj = pos[j]
    if pj == hp:
        return 'L'
    if pj == (hp + 1) % 3:
        return 'R'
    return 'O'


def edge_sig(ctx, i, j):
    """2-side signature of edge (i,j) seen at i, over sorted rem."""
    sol = ctx.sol if isinstance(ctx, lg.Ctx) else ctx
    rem = sorted(k for k in range(S) if k != i and k != j)
    return tuple(sol[i]['side'][(j, k)] for k in rem)


# ---------- winning gadget with charge/cap identification

def strip_detail(ctx, res):
    """Analyze a winning fan/link gadget: residual blocks, charge and
    cap vertices."""
    n, s = ctx.n, ctx.s
    R = {}
    for v, fw in res['fans'].items():
        Rd, _, _ = ctx.fan[(v, fw)]
        for k, t in Rd.items():
            R[k] = R.get(k, 0) + t
    h = res['pivot']
    for a, b, sig in res['edges']:
        Rd, _, _ = ctx.link[(min(a, b), max(a, b), h, sig)]
        for k, t in Rd.items():
            R[k] = R.get(k, 0) + t
    posblk = {v: [g for g in range(s - 1) if R.get((v, g), 0) > 0]
              for v in range(s)}
    negblk = {v: [g for g in range(s - 1) if R.get((v, g), 0) < 0]
              for v in range(s)}
    return {'posblk': {v: g for v, g in posblk.items() if g},
            'negblk': {v: g for v, g in negblk.items() if g}}


def winning(ctx):
    """First sufficient gadget in the enriched grammar."""
    bg = ex.block_gadgets(ctx)
    if bg is not None and bg[0] >= F(1):
        return ('block', {'bound': str(bg[0]), 'v': bg[1],
                          'caps': [(sorted(r), str(B), str(u))
                                   for r, B, u in bg[2]],
                          'charges': [(sorted(r), str(g))
                                      for r, g in bg[3]]})
    r = lg.pure_gadget(ctx)
    if r is not None and r['bound'] >= 1:
        return ('pure', {'bound': str(r['bound']),
                         'caps': [(v, sorted(rng)) for _, v, rng
                                  in r['caps']]})
    best = None
    fas = list(lg.fan_assignments(S))
    for h in range(S):
        outer = [v for v in range(S) if v != h]
        for r_ in range(0, len(outer) + 1):
            perms = [()] if r_ == 0 else itertools.permutations(outer,
                                                              r_)
            for perm in perms:
                for closed in (False, True):
                    for edges in lg.edge_lists(list(perm), closed):
                        for fa in fas:
                            res = ex.eval_chain2(ctx, h, edges, fa)
                            if res is not None and (
                                    best is None or
                                    res['bound'] > best['bound']):
                                best = res
                            if best is not None and \
                                    best['bound'] >= 1:
                                return ('strip', {
                                    'bound': str(best['bound']),
                                    'pivot': h, 'edges': best['edges'],
                                    'fans': best['fans'],
                                    'blocks': strip_detail(ctx, best)})
    return ('none', {'bound': None if best is None
                     else str(best['bound'])})


# ---------- main

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    profiles = [tuple(int(x) for x in args)] if args else \
        [(0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 0, 2), (0, 0, 1, 1)]
    maxrec = 1000000
    if '--max' in sys.argv:
        maxrec = int(sys.argv[sys.argv.index('--max') + 1])
    outjson = '--json' in sys.argv
    records = []
    agg = {}
    sat_hist = {}
    t0 = time.time()
    for d in profiles:
        ks = PROFILES[d]
        VV = ge.build_VV(list(ks), N, S)
        # speed: restrict k=3 vertices to saturated-bad variants only
        # (saturated requires k = n-1; non-k3 vertices can never be
        # saturated, so all-bad <=> every k3 vertex bad-saturated).
        for v in range(S):
            if ks[v] == N - 1:
                VV[v] = [vv for vv in VV[v] if vv_is_bad(vv)]
        sigvars = ge.build_sigvars(VV, S)
        n_cand = n_feas = 0
        for sol, idxs, sig in ge.gen_cases(list(ks), N, S,
                                           VV=VV, sigvars=sigvars):
            sol = [dict(x) for x in sol]
            sat = [v for v in range(S)
                   if heavy_pos(sol, v) is not None]
            if len(sat) < 2:
                continue
            bad = [v for v in sat if is_bad(sol, v)]
            key = (len(sat), len(bad))
            sat_hist[key] = sat_hist.get(key, 0) + 1
            if len(bad) < len(sat):
                continue
            n_cand += 1
            # pre-LP pattern tally (edge-side + tri_maybe only)
            for i, j in itertools.combinations(sat, 2):
                k = ('pre', fmode(sol, i), slot(sol, i, j),
                     fmode(sol, j), slot(sol, j, i))
                agg[k] = agg.get(k, 0) + 1
            st, lo = lp_feas_unclamped(sol)
            if st != 'bounded':
                sat_hist[('infeas', len(sat))] = \
                    sat_hist.get(('infeas', len(sat)), 0) + 1
                continue
            n_feas += 1
            if len(sat) >= 3:
                print(f'  !!! feasible all-bad nsat={len(sat)} '
                      f'd={d} idxs={idxs}', flush=True)
            pairs = []
            for i, j in itertools.combinations(sat, 2):
                pairs.append({
                    'i': i, 'j': j,
                    'mode_i': fmode(sol, i), 'slot_i': slot(sol, i, j),
                    'sig_i': edge_sig(sol, i, j),
                    'mode_j': fmode(sol, j), 'slot_j': slot(sol, j, i),
                    'sig_j': edge_sig(sol, j, i),
                })
            if '--nowin' in sys.argv:
                kind, win = 'skip', {}
            else:
                kind, win = winning(lg.Ctx(sol, N, S))
            rec = {
                'profile': d, 'idxs': idxs, 'sat': sat,
                'lo': None if lo is None else float(lo),
                'vdata': [{'order': sol[v]['order'],
                           'bits': sol[v]['bits'],
                           'qs': sol[v]['qs']} for v in range(S)],
                'pairs': pairs, 'kind': kind, 'win': win,
            }
            records.append(rec)
            for p in pairs:
                k = (p['mode_i'], p['slot_i'], p['mode_j'], p['slot_j'],
                     kind)
                agg[k] = agg.get(k, 0) + 1
            if n_feas % 100 == 0:
                print(f'  ... feas={n_feas} ({time.time()-t0:.0f}s)',
                      flush=True)
            if len(records) >= maxrec or time.time() - t0 > 1500:
                break
        print(f'd={d} cand={n_cand} feas_allbad={n_feas} '
              f'({time.time()-t0:.0f}s)', flush=True)
        if len(records) >= maxrec or time.time() - t0 > 1500:
            break
    print('sat/bad histogram (nsat, nbad):',
          dict(sorted(sat_hist.items(), key=lambda kv: str(kv[0]))))
    print('pair-pattern tally (mode_i,slot_i,mode_j,slot_j,kind):')
    for k in sorted(agg):
        print(f'  {k}: {agg[k]}')
    if outjson:
        fn = 'allbad_dump.json'
        with open(fn, 'w') as f:
            json.dump(records, f, indent=1, default=str)
        print('wrote', fn, len(records), 'records')


if __name__ == '__main__':
    main()
