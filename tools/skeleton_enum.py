"""Reusable skeleton enumeration for the s=4 remainder model.

A profile ks = (k0,k1,k2,k3) assigns an exponent target per vertex.
Realizable combinatorial skeletons are enumerated in two stages:

  1. signature level: (order, bits) per vertex, filtered by pairwise
     edge-side consistency (6 edges).
  2. q level: integer cell tuples per vertex (exponent-constrained),
     with triangle-sum interval pruning.

gen_cases(ks, mode, n) yields (sol, idxs) where sol is the list of 4
variant dicts and idxs their indices in the VV lists.
"""
import itertools
import remainder_check as rc

def build_VV(ks, n):
    return [rc.vertex_variants(v, ks[v],
                               tuple(x for x in range(4) if x != v), n)
            for v in range(4)]

def build_signatures(VV):
    sigvars = [dict() for _ in range(4)]
    for i in range(4):
        for idx, vv in enumerate(VV[i]):
            key = (vv['order'], tuple(sorted(vv['bits'].items())))
            sigvars[i].setdefault(key, []).append(idx)
    sig = {}
    for i in range(4):
        for j in range(4):
            if i == j:
                continue
            rem = sorted(k for k in range(4) if k != i and k != j)
            sig[(i, j)] = {}
            for key, idxs in sigvars[i].items():
                vv = VV[i][idxs[0]]
                sig[(i, j)][key] = \
                    (1 if vv['side'][(j, rem[0])] == 1 else 0) | \
                    (2 if vv['side'][(j, rem[1])] == 1 else 0)
    return sigvars, sig

def edge_ok(sig, i, j, ki, kj):
    return sig[(i, j)][ki] == (3 - sig[(j, i)][kj])

def consistent_signatures(sigvars, sig):
    keys = [list(s.keys()) for s in sigvars]
    for k0 in keys[0]:
        for k1 in keys[1]:
            if not edge_ok(sig, 1, 0, k1, k0):
                continue
            for k2 in keys[2]:
                if not (edge_ok(sig, 2, 0, k2, k0)
                        and edge_ok(sig, 2, 1, k2, k1)):
                    continue
                for k3 in keys[3]:
                    if (edge_ok(sig, 3, 0, k3, k0)
                            and edge_ok(sig, 3, 1, k3, k1)
                            and edge_ok(sig, 3, 2, k3, k2)):
                        yield (k0, k1, k2, k3)

def gen_cases(ks, n, VV=None, sigvars=None, sig=None):
    """Yield (sol, idxs, sigkey4) for every skeleton of profile ks."""
    if VV is None:
        VV = build_VV(ks, n)
    if sigvars is None or sig is None:
        sigvars, sig = build_signatures(VV)
    for k0, k1, k2, k3 in consistent_signatures(sigvars, sig):
        sol = [None] * 4
        for i0 in sigvars[0][k0]:
            sol[0] = VV[0][i0]
            for i1 in sigvars[1][k1]:
                sol[1] = VV[1][i1]
                for i2 in sigvars[2][k2]:
                    sol[2] = VV[2][i2]
                    if not rc.tri_maybe((0, 1, 2), sol, n):
                        continue
                    for i3 in sigvars[3][k3]:
                        sol[3] = VV[3][i3]
                        if not all(
                                rc.tri_maybe(t, sol, n)
                                for t in ((0, 1, 3), (0, 2, 3),
                                          (1, 2, 3))):
                            continue
                        yield (sol, (i0, i1, i2, i3),
                               (k0, k1, k2, k3))
                    sol[2] = None
                sol[1] = None
            sol[0] = None
