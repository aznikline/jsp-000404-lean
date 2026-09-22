"""Lane A experiment: LOW selection theorem structure mining.

For each consistent skeleton of a deficit profile, evaluate
restricted gadget families and (for samples) the full enumerator;
mine the structure of skeletons with no level-1 gadget.
"""
import sys, json, itertools, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import generic_model as gm
import link_graph as lg
import generic_cegis as gce

ZERO = F(0)


def profile_data(sol, n, s):
    """Per-vertex B_v, nz_v, d_v, K_v (fan charge bound)."""
    out = []
    for v in range(s):
        vv = sol[v]
        qs = vv['qs']
        order = vv['order']
        bits = vv['bits']
        B = n - sum(qs)
        nz = sum(1 for q in qs if q >= 1)
        d = B + nz - 1
        # K_v: bit-changes over empty non-wrap gaps
        pos = {d_: t for t, d_ in enumerate(order)}
        K = 0
        m = s - 1
        for t in range(m - 1):          # gaps 0..m-2 are non-wrap
            if qs[t] == 0:
                a, b = order[t], order[t + 1]
                if bits[a] != bits[b]:
                    K += 1
        out.append(dict(B=B, nz=nz, d=d, K=K, qs=tuple(qs),
                        order=tuple(order),
                        bits=tuple(bits[x] for x in order)))
    return out


def fan_bound(pd_v):
    return pd_v['K'] - pd_v['B']


def main():
    n = s = 4
    ks = [3, 2, 2, 1]
    VV = ge.build_VV(ks, n, s)
    sigvars = ge.build_sigvars(VV, s)
    cnt = 0
    t0 = time.time()
    nogad = []
    for sol, idxs, sigk in ge.gen_cases(ks, n, s, VV=VV, sigvars=sigvars):
        cnt += 1
        sol = [dict(x) for x in sol]
        pd = profile_data(sol, n, s)
        fb = max(fan_bound(p) for p in pd)
        if fb >= 1:
            continue
        # no level-1 fan gadget: full check on a subsample
        if len(nogad) < 40:
            best = lg.enumerate_max(sol, n, s)
            bb = None if best is None else best['bound']
            nogad.append((idxs, sigk, pd,
                          None if bb is None else str(bb)))
    print(f'leaves={cnt}  no-fan-L1={len(nogad)} ({time.time()-t0:.0f}s)')
    for idxs, sigk, pd, bb in nogad[:40]:
        W = sum(F(1, 2) ** p['d'] for p in pd)
        print(f'idxs={idxs} W={float(W):.3f} best={bb}')
        for v, p in enumerate(pd):
            print(f'   v{v} B={p["B"]} nz={p["nz"]} d={p["d"]} '
                  f'K={p["K"]} qs={p["qs"]} bits={p["bits"]} '
                  f'order={p["order"]}')


if __name__ == '__main__':
    main()
