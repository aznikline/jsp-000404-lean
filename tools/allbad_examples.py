"""Dump 2 representative winning gadgets per selector branch."""
import sys, json, collections
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import link_graph as lg
from allbad_dump import PROFILES, N, S, slot, fmode
from allbad_selector import select, rebuild


def main():
    fn = sys.argv[1] if len(sys.argv) > 1 else 'allbad_dump.json'
    recs = json.load(open(fn))
    ks = PROFILES[tuple(recs[0]['profile'])]
    VV = ge.build_VV(list(ks), N, S)
    look = [{(vv['order'], tuple(sorted(vv['bits'].items())), vv['qs']): vv
            for vv in VV[v]} for v in range(S)]
    seen = collections.Counter()
    for r in recs:
        sol = rebuild(r, look)
        ctx = lg.Ctx(sol, N, S)
        br, res = select(ctx, set(r['sat']))
        seen[br] += 1
        if seen[br] <= 2:
            p = r['pairs'][0]
            print(f'== {br} rec idxs={r["idxs"]} sat={r["sat"]} '
                  f'slots=({p["slot_i"]},{p["slot_j"]}) lo={r["lo"]}')
            print('   qs:', [tuple(v['qs']) for v in sol])
            if isinstance(res, dict):
                print('   res:', {k: (str(v) if not isinstance(
                    v, (int, float)) else v)
                    for k, v in res.items() if k in (
                        'bound', 'con', 'dc', 'K', 'B', 'u', 'resid',
                        'fans', 'edges', 'caps', 'blocks')})
            else:
                print('   res:', res)
    print(dict(seen))


if __name__ == '__main__':
    main()
