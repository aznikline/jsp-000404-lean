"""Per-vertex analysis of the local-gadget mechanism.

At a saturated vertex v (qs = perm of (n,0,...,0), B_v = 0):
  * pure cap  := exists direct arc with q_arc >= n
  * charge    := exists comp arc with q_arc = 0  (gain 1 >= B_v+1)
Failure modes (s=4, m=3): F1 all-bits-equal & big wrap gap;
F2 (b2,b3)=(0,1) & big=b; F3 (b2,b3)=(1,1) & big=a.

For each feasible skeleton in W>5/2 profiles report: number of
saturated vertices, their modes, and which vertex supplied the
winning local gadget.
"""
import sys, itertools, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import generic_model as gm
import generic_cegis as gce
import link_graph as lg
from scan_high import PROFILES, lp_feas

N = S = 4


def vertex_mode(ctx, v):
    """Classify saturated vertex v: 'cap', 'charge', or failure F*."""
    qs = ctx.qs_b[v]
    n = ctx.n
    if sum(qs) != n or sorted(qs) != [0] * (len(qs) - 1) + [n]:
        return 'nonsat'
    big = qs.index(n)
    bits = ctx.bits_b[v]
    order = ctx.sol[v]['order']
    b2, b3 = bits[order[1]], bits[order[2]]
    # arcs: A12={0}, A23={1}, A13={0,1} (gap indices)
    comp = {(0, 1): b2 == 1, (1, 2): b2 != b3, (0, 2): b3 == 1}
    arcss = {(0, 1): frozenset([0]), (1, 2): frozenset([1]),
             (0, 2): frozenset([0, 1])}
    # pure cap: direct arc with q_arc >= n
    for pr, arc in arcss.items():
        if not comp[pr] and sum(qs[g] for g in arc) >= n:
            return 'cap'
    # charge: comp arc with q_arc = 0
    for pr, arc in arcss.items():
        if comp[pr] and sum(qs[g] for g in arc) == 0:
            return 'charge'
    # failure modes
    if (b2, b3) == (0, 0):
        return 'F1'   # must have big==2 (wrap) else cap fired
    if (b2, b3) == (0, 1):
        return 'F2'
    return 'F3'


def main():
    max_feas = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    for d, ks in PROFILES:
        VV = ge.build_VV(list(ks), N, S)
        sigvars = ge.build_sigvars(VV, S)
        feas = 0
        modecount = {}
        winners = {}
        fails = []
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
            for m in modes:
                modecount[m] = modecount.get(m, 0) + 1
            res = lg.pure_gadget(ctx)
            kind = None
            if res is not None and res['bound'] >= 1:
                kind = 'pure'
            else:
                for v in range(S):
                    r = lg.eval_chain(ctx, 0, [], {v: 1})
                    if r is not None and r['bound'] >= 1:
                        kind = ('fan+', v, modes[v])
                        break
                    r = lg.eval_chain(ctx, 0, [], {v: -1})
                    if r is not None and r['bound'] >= 1:
                        kind = ('fan-', v, modes[v])
                        break
            if kind is None:
                fails.append(idxs)
                print(f'  NOLOCAL d={d} idxs={idxs} modes={modes}',
                      flush=True)
            else:
                winners[kind] = winners.get(kind, 0) + 1
            if feas >= max_feas or time.time() - t0 > 600:
                break
        print(f'd={d} feas={feas} modes={modecount} '
              f'winners={winners} fails={len(fails)}', flush=True)


if __name__ == '__main__':
    main()
