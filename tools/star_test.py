"""Uniform-template test over all-fail feasible skeletons.

Candidate canonical gadgets (x = a failing saturated vertex):
  star_x  : fan_x(+1) + sum over all pairs {a,b} of others of
            -D{x,a,b}        (3 links at s=4)
  path_x(perm): fan_x(+1) - D{x,p0,p1} - D{x,p1,p2}
            (2-link strip, all 6 path orders)
  ystar   : same with fan_y

We test whether SOME canonical gadget reaches bound >= 1 on every
all-fail feasible skeleton, and which templates are needed.
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


def templates(ctx, x, y, others):
    """Yield (name, edges, fans) gadgets."""
    zw = others
    yield 'star_x', x, [(a, b, -1) for a, b in
                        itertools.combinations(zw + [y], 2)], {x: 1}
    for p in itertools.permutations([y] + zw):
        yield (f'path_x{p}', x,
               [(p[0], p[1], -1), (p[1], p[2], -1)], {x: 1})
    for p in itertools.permutations([x] + zw):
        yield (f'path_y{p}', y,
               [(p[0], p[1], -1), (p[1], p[2], -1)], {y: 1})
    # two fans + one triangle link (any triangle/sign)
    for t in itertools.combinations(range(S), 3):
        for sg in (1, -1):
            for h in t:
                a, b = [v for v in t if v != h]
                yield (f'T{t}{sg:+d}h{h}', h, [(a, b, sg)],
                       {x: 1, y: 1})


def main():
    for d, ks in [((0, 0, 1, 1), (3, 3, 2, 2)),
                  ((0, 0, 1, 2), (3, 3, 2, 1)),
                  ((0, 0, 1, 3), (3, 3, 2, 0))]:
        VV = ge.build_VV(list(ks), N, S)
        sigvars = ge.build_sigvars(VV, S)
        feas = 0
        cover = {}
        nocov = []
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
            others = [v for v in range(S) if v not in sat]
            hits = []
            for name, piv, edges, fans in templates(ctx, x, y, others):
                r = lg.eval_chain(ctx, piv, list(edges), dict(fans))
                if r is not None and r['bound'] >= 1:
                    hits.append(name.split('(')[0])
            # local gadgets
            r = lg.pure_gadget(ctx)
            if r is not None and r['bound'] >= 1:
                hits.append('pure')
            for v in range(S):
                r = lg.eval_chain(ctx, 0, [], {v: 1})
                if r is not None and r['bound'] >= 1:
                    hits.append(f'fan{v}')
            key = frozenset(h.split('(')[0] for h in hits)
            for h in key:
                cover[h] = cover.get(h, 0) + 1
            if not hits:
                nocov.append((idxs, modes))
                print('  NOCOVER', idxs, modes, flush=True)
            if feas >= 1200 or time.time() - t0 > 500:
                break
        print(f'd={d} feas={feas} nocov={len(nocov)} cover={cover}',
              flush=True)


if __name__ == '__main__':
    main()
