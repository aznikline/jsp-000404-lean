"""Deep dive: feasible skeletons with BOTH saturated vertices failing.

For each, record for the two third vertices z,w:
  * angle ∠z{x,y}: direct/comp, arc size, q_arc
  * z's q-tuple / B_z
and the winning gadget (family + bound).
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


def main():
    for d, ks in [((0, 0, 1, 1), (3, 3, 2, 2)),
                  ((0, 0, 1, 2), (3, 3, 2, 1)),
                  ((0, 0, 1, 3), (3, 3, 2, 0))]:
        VV = ge.build_VV(list(ks), N, S)
        sigvars = ge.build_sigvars(VV, S)
        feas = 0
        rows = []
        seen_pat = {}
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
            res = lg.enumerate_max(sol, N, S)
            pat = (
                modes[x], modes[y],
                anginfo(ctx, z, x, y), anginfo(ctx, w, x, y),
                sol[z]['qs'], sol[w]['qs'],
                None if res is None else str(res['bound']),
                None if res is None else
                (tuple(res.get('edges', [])),
                 tuple(sorted(res['fans'].items())),
                 res.get('pure', False)))
            if pat not in seen_pat:
                seen_pat[pat] = idxs
                rows.append((idxs, modes, z, w, res, sol, ctx))
            if feas >= 700 or time.time() - t0 > 400:
                break
        print(f'=== d={d} feas={feas} distinct-patterns={len(rows)}')
        for idxs, modes, z, w, res, sol, ctx in rows[:14]:
            print(f'idxs={idxs} modes={modes}')
            print(f'  x,y=0,1 see each other: '
                  f'pos_x(y)={sol[0]["order"].index(1)} '
                  f'pos_y(x)={sol[1]["order"].index(0)}')
            for v in (z, w):
                print(f'  v{v} qs={sol[v]["qs"]} B={N - sum(sol[v]["qs"])}'
                      f' ord={sol[v]["order"]} '
                      f'bits={dict(sorted(sol[v]["bits"].items()))} '
                      f'ang[{x},{y}]={anginfo(ctx, v, x, y)}')
            if res:
                print(f'  best bound={res["bound"]} pure={res.get("pure")} '
                      f'fans={res["fans"]} edges={res["edges"]} '
                      f'c={res["c"]} u={res["u"]} C={res["C"]} '
                      f'K={res["K"]} Bcap={res["Bcap"]}')


if __name__ == '__main__':
    main()
