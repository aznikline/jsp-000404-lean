"""Fan-pair landscape: for each skeleton, which endpoint fan sets
still force delta >= 1/2, and with what residual score.

For each fan subset S (|S| in 1..3) restrict equalities to
{fans in S} + {all triangles}, keep all inequalities, run exact LP.
If bounded with min delta >= 1/2 (or infeasible), extract the
certificate's residual parameters (K, C, B, u) via residual_map.

Score bookkeeping (residual_map convention, un-halved):
    residual:  P - U - c*delta = C
    delta >= (K - B - C)/(c+u)
    capacity:  (c+u)/2 <= K - B - C   <=>  K + SbT >= B_L+B_R+Bcap+1

Usage: python3 fan_pairs.py s4 | s5
"""
import sys, json, itertools
sys.path.insert(0, '.')
from fractions import Fraction as F
import residual_map as rm

def restrict_lp(E, sol, n, fanset, s):
    E.ORIG.clear()
    E.build_case(sol, n, 'A')
    full = {E.orig(i)[0] for i in range(len(E.ORIG))}
    keep = {f'V{v} Σgap=π' for v in fanset}
    skip = {d for d in full - rm.FIXED
            if d.startswith('V') and d not in keep}
    E.ORIG.clear()
    b = E.build_case(sol, n, 'A', skip=skip)
    ineqs, eqs = b
    ineqs = E.substitute(eqs, ineqs)
    st, lo, y = rm.glp_min_delta(ineqs, E.CONST, E.DELTA)
    return st, lo, (rm.extract_cert(E, ineqs, y)
                    if st == 'bounded' else None)

def run(dd, E, build_sol, n, s, out_fn):
    results = []
    for rec in dd:
        sol = build_sol(rec)
        ks = rec['profile']['ks']
        d = rec['profile']['deficits']
        qs = rec['qs']
        pos = {v: sum(1 for q in qs[v] if q > 0) for v in range(s)}
        budget = {v: d[v] + 1 - pos[v] for v in range(s)}
        row = {'tag': rec['tag'], 'ks': ks, 'deficits': d,
               'budget': {str(k): v for k, v in budget.items()},
               'pairs': []}
        for r_ in (1, 2):
            for sub in itertools.combinations(range(s), r_):
                st, lo, W = restrict_lp(E, sol, n, sub, s)
                ent = {'fans': list(sub), 'status': st,
                       'min_delta': str(lo)}
                if st == 'bounded' and W:
                    res = rm.analyze(E, W, E.DELTA, E.CONST)
                    ent.update({k: res.get(k) for k in
                                ('verdict', 'c', 'u', 'B', 'K', 'C',
                                 'capacity_slack')})
                if (st == 'infeasible'
                        or (st == 'bounded' and lo >= F(1, 2))):
                    ent['works'] = True
                row['pairs'].append(ent)
        results.append(row)
        work = [p['fans'] for p in row['pairs'] if p.get('works')]
        print(f"{rec['tag'][:36]:38s} budget={budget} "
              f"working={work}", flush=True)
    json.dump(results, open(out_fn, 'w'), indent=1)
    print(f'-> {out_fn}')

def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 's4'
    if which == 's4':
        import skeleton_enum as sen
        E = rm.load_s4()
        data = json.load(open('chain_dump_s4.json'))
        VV = sen.build_VV((3, 2, 2, 1), 4)
        run(data, E, lambda r: [VV[v][r['idxs'][v]] for v in range(4)],
            4, 4, 'fan_pairs_s4.json')
    else:
        import generic_enum as ge
        E = rm.load_g()
        data = json.load(open('chain_dump_s5.json'))
        cache = {}
        def build_sol(rec):
            fn = rec['tag'].split(':')[0]
            if fn not in cache:
                ks = json.load(open(fn))['ks']
                cache[fn] = ge.build_VV(ks, 5, 5)
            VV = cache[fn]
            return [VV[v][rec['idxs'][v]] for v in range(5)]
        run(data, E, build_sol, 5, 5, 'fan_pairs_s5.json')

if __name__ == '__main__':
    main()
