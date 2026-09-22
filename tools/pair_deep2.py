"""Deep dive v2 (fast): feasible skeletons with BOTH saturated
vertices failing.  Gadget search restricted to observed families:
pure / fan1 / fan+ <=2 links (any pivot/signs) / <=2 fans + <=1 link.

For each pattern record the structure of the two third vertices.
"""
import sys, itertools, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import generic_model as gm
import link_graph as lg
from scan_high import lp_feas
from scan_vertices import vertex_mode

N = S = 4


def anginfo(ctx, v, a, b):
    comp, rng, q = ctx.ang[v][tuple(sorted((a, b)))]
    return ('C' if comp else 'D', len(rng), q)


def small_max(ctx):
    """Best among pure/fan1/fan+<=2links/2fans+<=1link."""
    best = lg.pure_gadget(ctx)
    s = ctx.s
    def acc(r):
        nonlocal best
        if r is not None and (best is None or r['bound'] > best['bound']):
            best = r
    one_fan = [{v: fw} for v in range(s) for fw in (1, -1)]
    two_fan = [{v1: f1, v2: f2} for v1 in range(s)
               for v2 in range(v1 + 1, s)
               for f1 in (1, -1) for f2 in (1, -1)]
    for fa in one_fan + two_fan:
        acc(lg.eval_chain(ctx, 0, [], fa))
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        l1 = [[(a, b, sg)] for a, b in itertools.combinations(outer, 2)
              for sg in (1, -1)]
        l2 = [e1 + e2 for i, e1 in enumerate(l1) for e2 in l1[i:]]
        for fa in [{}] + one_fan + two_fan:
            for ed in l1:
                acc(lg.eval_chain(ctx, h, ed, fa))
        for fa in [{}] + one_fan:
            for ed in l2:
                acc(lg.eval_chain(ctx, h, ed, fa))
    return best


def main():
    for d, ks in [((0, 0, 1, 1), (3, 3, 2, 2)),
                  ((0, 0, 1, 2), (3, 3, 2, 1)),
                  ((0, 0, 1, 3), (3, 3, 2, 0))]:
        VV = ge.build_VV(list(ks), N, S)
        sigvars = ge.build_sigvars(VV, S)
        feas = 0
        rows = []
        seen_pat = set()
        t0 = time.time()
        for sol, idxs, sig in ge.gen_cases(list(ks), N, S,
                                         VV=VV, sigvars=sigvars):
            sol = [dict(x) for x in sol]
            st, lo = lp_feas(sol)
            if st != 'bounded':
                continue
            feas += 1
            ctx = lg.Ctx(sol, N, S)
            modes = [vertex_mode(ctx, v) for v in range(S)]
            sat = [v for v in range(S) if modes[v] != 'nonsat']
            if len(sat) != 2 or not all(
                    modes[v] in ('F1', 'F2', 'F3') for v in sat):
                continue
            x, y = sat
            zw = [v for v in range(S) if v not in sat]
            z, w = zw
            pat = (
                modes[x], modes[y],
                sol[x]['order'], sol[y]['order'],
                anginfo(ctx, z, x, y), anginfo(ctx, w, x, y),
                sol[z]['qs'], sol[w]['qs'])
            if pat in seen_pat:
                continue
            seen_pat.add(pat)
            res = small_max(ctx)
            rows.append((idxs, modes, x, y, z, w, res, sol, ctx))
            if time.time() - t0 > 400:
                break
        print(f'=== d={d} feas={feas} distinct={len(rows)}')
        for idxs, modes, x, y, z, w, res, sol, ctx in rows:
            print(f'idxs={idxs} modes={modes} '
                  f'ordx={sol[x]["order"]} ordy={sol[y]["order"]} '
                  f'pos_xy=({sol[x]["order"].index(y)},'
                  f'{sol[y]["order"].index(x)})')
            for v in (z, w):
                print(f'   v{v} qs={sol[v]["qs"]} ord={sol[v]["order"]} '
                      f'bits={dict(sorted(sol[v]["bits"].items()))} '
                      f'ang[{x}{y}]={anginfo(ctx, v, x, y)}')
            if res:
                print(f'   best={res["bound"]} pure={res.get("pure")} '
                      f'fans={res["fans"]} edges={res["edges"]} '
                      f'c={res["c"]} u={res["u"]} C={res["C"]} '
                      f'K={res["K"]} Bcap={res["Bcap"]}')
            else:
                print('   best=None')


if __name__ == '__main__':
    main()
