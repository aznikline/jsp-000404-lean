"""Full all-bad scan WITHOUT LP: enumerate every signature-consistent
all-bad skeleton (edge-side + tri_maybe pruning only) across the
W>5/2 profiles and run the deterministic gadget selector.

This measures whether the combinatorial construction covers every
edge-consistent all-bad skeleton — including LP-infeasible ones —
supporting the claim that `SkeletonConsistent` is not needed for
the strip construction.

Usage: python3 allbad_scan.py [d0 d1 d2 ...] [--max N] [--sel]
  --sel  run the gadget selector on every candidate (default:
         tally only).
"""
import sys, itertools, time, collections
sys.path.insert(0, '.')
import generic_enum as ge
import link_graph as lg
from allbad_dump import heavy_pos, is_bad, vv_is_bad, slot, fmode, \
    PROFILES, N, S
from allbad_selector import select


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    profiles = [tuple(int(x) for x in args)] if args else \
        list(PROFILES)
    maxrec = 10**9
    if '--max' in sys.argv:
        maxrec = int(sys.argv[sys.argv.index('--max') + 1])
    dosel = '--sel' in sys.argv
    for d in profiles:
        ks = PROFILES[d]
        VV = ge.build_VV(list(ks), N, S)
        for v in range(S):
            if ks[v] == N - 1:
                VV[v] = [vv for vv in VV[v] if vv_is_bad(vv)]
        sigvars = ge.build_sigvars(VV, S)
        tally = collections.Counter()
        slots = collections.Counter()
        n_cand = 0
        t0 = time.time()
        none_recs = []
        for sol, idxs, sig in ge.gen_cases(list(ks), N, S,
                                           VV=VV, sigvars=sigvars):
            sol = [dict(x) for x in sol]
            sat = [v for v in range(S)
                   if heavy_pos(sol, v) is not None]
            if len(sat) < 2:
                continue
            bad = [v for v in sat if is_bad(sol, v)]
            if len(bad) < len(sat):
                continue
            n_cand += 1
            for i, j in itertools.combinations(sat, 2):
                slots[(slot(sol, i, j), slot(sol, j, i))] += 1
            if dosel:
                br, res = select(lg.Ctx(sol, N, S), set(sat))
                tally[br] += 1
                if br == 'NONE':
                    none_recs.append((idxs, sat))
                    if len(none_recs) <= 10:
                        print('  NONE', idxs, sat, flush=True)
            if n_cand % 5000 == 0:
                print(f'  ... {n_cand} ({time.time()-t0:.0f}s) '
                      f'{dict(tally)}', flush=True)
            if n_cand >= maxrec or time.time() - t0 > 2400:
                break
        print(f'd={d} allbad_candidates={n_cand} '
              f'slots={dict(slots)}')
        print(f'  selector: {dict(tally)}  NONE={len(none_recs)} '
              f'({time.time()-t0:.0f}s)', flush=True)


if __name__ == '__main__':
    main()
