"""Count no-fan-L1 skeletons and mine gadget shapes (profile arg)."""
import sys, json, itertools, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import link_graph as lg
from lane_a import profile_data, fan_bound


def main():
    n = s = 4
    ks = json.loads(sys.argv[1]) if len(sys.argv) > 1 else [3, 2, 2, 1]
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    VV = ge.build_VV(ks, n, s)
    sigvars = ge.build_sigvars(VV, s)
    cnt = nofan = 0
    t0 = time.time()
    shapes = {}
    checked = 0
    for sol, idxs, sigk in ge.gen_cases(ks, n, s, VV=VV, sigvars=sigvars):
        cnt += 1
        pd = profile_data(sol, n, s)
        if max(fan_bound(p) for p in pd) >= 1:
            continue
        nofan += 1
        if checked < limit:
            sol = [dict(x) for x in sol]
            best = lg.enumerate_max(sol, n, s)
            checked += 1
            key = None if best is None else (
                str(best['bound']),
                'pure' if best.get('pure') else
                (best['pivot'], len(best['edges']),
                 tuple(sorted(best['fans'].items()))))
            shapes[key] = shapes.get(key, 0) + 1
            if best is None or best['bound'] < F(1, 2):
                print('*** NO L1 GADGET', idxs, sigk)
                for v, p in enumerate(pd):
                    print('   ', v, p)
    print(f'leaves={cnt} nofanL1={nofan} checked={checked} '
          f'({time.time()-t0:.0f}s)')
    for k, c in sorted(shapes.items(), key=lambda t: str(t[0])):
        print(' ', c, k)


if __name__ == '__main__':
    main()
