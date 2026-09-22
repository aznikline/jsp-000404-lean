"""Exact Farkas certificate for a recorded all-bad skeleton.

Usage: python3 cert_allbad.py <record_json_index> [--pair]
Rebuilds the skeleton from allbad_dump.json vdata, runs the exact LP
(unclamped delta), prints ORIG constraints with dual weights.
"""
import sys, json
sys.path.insert(0, '.')
import generic_enum as ge
import generic_model as gm
import remainder_check as rc

N = S = 4


def rebuild(rec, ks):
    VV = ge.build_VV(list(ks), N, S)
    look = [{(vv['order'], tuple(sorted(vv['bits'].items())), vv['qs']): vv
            for vv in VV[v]} for v in range(S)]
    sol = []
    for v, vd in enumerate(rec['vdata']):
        key = (tuple(vd['order']),
               tuple(sorted((int(k), b) for k, b in vd['bits'].items())),
               tuple(vd['qs']))
        sol.append(look[v][key])
    return sol


def main():
    fn = sys.argv[1] if len(sys.argv) > 1 else 'allbad_dump.json'
    pos = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    ks = tuple(int(x) for x in sys.argv[3:7]) if len(sys.argv) > 6 \
        else (3, 3, 2, 2)
    recs = json.load(open(fn))
    rec = recs[pos]
    sol = rebuild(rec, ks)
    for v in range(S):
        vv = sol[v]
        print(f"v{v}: order={vv['order']} bits="
              f"{dict(sorted(vv['bits'].items()))} qs={vv['qs']}")
    print('pairs:', rec['pairs'], 'float lo:', rec['lo'])
    gm.ORIG.clear()
    ineqs, eqs = gm.build_case(sol, N, 'A', skip={'δ<1'})
    ineqs = gm.substitute(eqs, ineqs)
    st, lo, y = rc.lp_min_delta(ineqs)
    print(f'exact LP (unclamped): {st} min delta = {lo}')
    if st != 'bounded':
        return
    W, combo = gm.extract_cert(ineqs, y)
    print('certificate:')
    for cid, w in sorted(W.items()):
        if w:
            print(f'  {w} x [{gm.ORIG[cid].desc}]')
    print('combo:', combo)


if __name__ == '__main__':
    main()
