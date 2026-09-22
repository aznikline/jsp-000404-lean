"""Dump full structure + enumerate_max for specific all-fail NOCOV
skeletons."""
import sys, itertools
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import generic_model as gm
import link_graph as lg
from scan_high import lp_feas
from scan_vertices import vertex_mode

N = S = 4


def run(ks, targets):
    VV = ge.build_VV(list(ks), N, S)
    sigvars = ge.build_sigvars(VV, S)
    for sol, idxs, sig in ge.gen_cases(list(ks), N, S, VV=VV,
                                     sigvars=sigvars):
        if tuple(idxs) not in targets:
            continue
        sol = [dict(x) for x in sol]
        st, lo = lp_feas(sol)
        ctx = lg.Ctx(sol, N, S)
        print(f'=== idxs={idxs} lp={st}:{lo}')
        for v in range(S):
            print(f'  v{v}: order={sol[v]["order"]} bits='
                  f'{dict(sorted(sol[v]["bits"].items()))} '
                  f'qs={sol[v]["qs"]} mode={vertex_mode(ctx, v)}')
        for v in range(S):
            for (a, b), (comp, rng, q) in sorted(ctx.ang[v].items()):
                print(f'    ang v{v} {{{a},{b}}}: '
                      f'{"comp" if comp else "dir "} '
                      f'rng={sorted(rng)} q={q}')
        res = lg.enumerate_max(sol, N, S)
        print('  BEST', {k: res[k] for k in
                         ('bound', 'c', 'u', 'C', 'K', 'Bcap',
                          'pivot', 'edges', 'fans', 'pure')
                         if k in res})
        targets.discard(tuple(idxs))
        if not targets:
            return


run((3, 3, 2, 1), {(0, 23, 75, 50), (0, 28, 75, 50), (0, 36, 21, 9)})
