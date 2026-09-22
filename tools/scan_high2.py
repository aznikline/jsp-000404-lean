"""Detailed scan: for W>5/2 skeletons print the winning gadget and
dump full detail for cases beyond pure/fan1.  Also test whether
INFEASIBLE skeletons admit bound>=1 (would mean consistency is not
needed for the existence statement).
"""
import sys, json, itertools, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import generic_model as gm
import generic_cegis as gce
import link_graph as lg
from scan_high import PROFILES, lp_feas, staged_max

N = S = 4


def describe(ctx, res):
    if res is None:
        return 'None'
    out = dict(bound=str(res['bound']), c=str(res['c']), u=str(res['u']),
               C=str(res['C']), K=str(res['K']), Bcap=str(res['Bcap']))
    if res.get('pure'):
        out['caps'] = [(v, sorted(r), str(q)) for _, v, r in
                       [(t, t[1], t[2]) for t in res['caps']]
                       for q in [sum(ctx.qs_b[v][g] for g in r)]]
    else:
        out['fans'] = res['fans']
        out['edges'] = res['edges']
        out['pivot'] = res['pivot']
    return out


def sol_brief(sol):
    return [(v['order'], tuple(sorted(v['bits'].items())), v['qs'])
            for v in sol]


def main():
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    for d, ks in PROFILES:
        VV = ge.build_VV(list(ks), N, S)
        sigvars = ge.build_sigvars(VV, S)
        tally = {}
        seen = infs = 0
        t0 = time.time()
        for sol, idxs, sig in ge.gen_cases(list(ks), N, S,
                                         VV=VV, sigvars=sigvars):
            sol = [dict(x) for x in sol]
            st, lo = lp_feas(sol)
            feas = (st == 'bounded')
            if not feas:
                infs += 1
            ctx = lg.Ctx(sol, N, S)
            fam, res = staged_max(ctx)
            bb = None if res is None else res['bound']
            key = (fam, 'F' if feas else 'INF',
                   None if bb is None else (str(bb) if bb < 1 else '≥1'))
            tally[key] = tally.get(key, 0) + 1
            if (fam not in ('pure', 'fan1')) or (bb is not None and bb < 1) or bb is None:
                print(f'  d={d} idxs={idxs} feas={feas} fam={fam} '
                      f'bb={bb} sol={sol_brief(sol)}',
                      flush=True)
                print(f'    res={describe(ctx, res)}', flush=True)
            seen += 1
            if seen >= cap or time.time() - t0 > 240:
                break
        print(f'd={d} ks={ks} seen={seen} inf={infs} tally={tally} '
              f'({time.time()-t0:.0f}s)', flush=True)


if __name__ == '__main__':
    main()
