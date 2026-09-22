"""Full small-gadget coverage test over all-fail feasible skeletons.

Grammar: any subset of fans (weights +-1) and any list of <=2 links
(any pivot, any sign), plus pure caps.  Reports the minimal gadget
"size" needed and whether <=2 links always suffices.
"""
import sys, itertools, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import generic_model as gm
import link_graph as lg
import eval_ext as ex
from scan_high import lp_feas
from scan_vertices import vertex_mode

N = S = 4


def all_links(s):
    """All (pivot, (a,b,sig)) with triangle {a,b,pivot}."""
    out = []
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        for a, b in itertools.combinations(outer, 2):
            for sg in (1, -1):
                out.append((h, a, b, sg))
    return out


def gadgets(s):
    """Yield (tag, pivot, edges, fans): |fans|<=2, |links|<=2, all
    links sharing one pivot h."""
    fansets = [{}]
    for v in range(s):
        for f in (1, -1):
            fansets.append({v: f})
    for v1 in range(s):
        for v2 in range(v1 + 1, s):
            for f1 in (1, -1):
                for f2 in (1, -1):
                    fansets.append({v1: f1, v2: f2})
    for h in range(s):
        outer = [v for v in range(s) if v != h]
        L = [(a, b, sg)
             for a, b in itertools.combinations(outer, 2)
             for sg in (1, -1)]
        linksets = [[]] + [[l] for l in L] + \
            [list(p) for p in itertools.combinations(L, 2)]
        for fa in fansets:
            for ls in linksets:
                yield ('fans' if not ls else 'mix', h, ls, fa)


def main():
    for d, ks in [((0, 0, 1, 1), (3, 3, 2, 2)),
                  ((0, 0, 1, 2), (3, 3, 2, 1)),
                  ((0, 0, 1, 3), (3, 3, 2, 0))]:
        VV = ge.build_VV(list(ks), N, S)
        sigvars = ge.build_sigvars(VV, S)
        feas = 0
        nocov = []
        tally = {}
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
            r = lg.pure_gadget(ctx)
            hit = 'pure' if (r and r['bound'] >= 1) else None
            if hit is None:
                bg = ex.block_gadgets(ctx)
                if bg is not None and bg[0] >= F(1):
                    hit = 'block'
            if hit is None:
                for tag, piv, ed, fa in gadgets(S):
                    r = lg.eval_chain(ctx, piv, ed, fa)
                    if r is not None and r['bound'] >= 1:
                        hit = (len(ed), len(fa), tag)
                        break
            if hit is None:
                nocov.append(idxs)
                print('  NOCOV', idxs, modes, flush=True)
            else:
                tally[str(hit)] = tally.get(str(hit), 0) + 1
            if time.time() - t0 > 480:
                break
        print(f'd={d} feas={feas} nocov={len(nocov)} tally={tally}',
              flush=True)


if __name__ == '__main__':
    main()
