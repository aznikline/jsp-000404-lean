"""Count feasible skeletons where EVERY saturated vertex is in a local
failure mode (F1/F2/F3), and inspect what gadget rescues them."""
import sys, itertools, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import generic_model as gm
import link_graph as lg
from scan_high import PROFILES, lp_feas
from scan_vertices import vertex_mode

N = S = 4


def main():
    max_feas = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    for d, ks in PROFILES:
        VV = ge.build_VV(list(ks), N, S)
        sigvars = ge.build_sigvars(VV, S)
        feas = 0
        allfail = 0
        rescued = {}
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
            satmodes = [m for m in modes if m != 'nonsat']
            if not satmodes or not all(
                    m in ('F1', 'F2', 'F3') for m in satmodes):
                continue
            allfail += 1
            res = lg.enumerate_max(sol, N, S)
            key = (tuple(sorted(set(satmodes))),
                   None if res is None else str(res['bound']),
                   None if res is None else
                   (len(res.get('edges', [])), len(res['fans']),
                    res.get('pure', False)))
            rescued[key] = rescued.get(key, 0) + 1
            if allfail <= 8:
                print(f'  ALLFAIL d={d} idxs={idxs} modes={modes} '
                      f'best={None if res is None else res["bound"]} '
                      f'edges={None if res is None else res["edges"]} '
                      f'fans={None if res is None else res["fans"]} '
                      f'pure={None if res is None else res.get("pure")}',
                      flush=True)
            if feas >= max_feas or time.time() - t0 > 400:
                break
        print(f'd={d} feas={feas} allfail={allfail} rescued={rescued}',
              flush=True)


if __name__ == '__main__':
    main()
