"""s-generic skeleton enumeration.

Signature-level DFS over (order, bits) per vertex with edge-side
consistency pruning, then leaf-level DFS over q-tuples with
triangle-sum interval pruning (generic_model.tri_maybe).

gen_cases(ks, n, s) yields (sol, idxs, sigkey) for each skeleton.
"""
from itertools import combinations
import generic_model as gm

def build_VV(ks, n, s):
    return [gm.vertex_variants(
                v, ks[v], tuple(x for x in range(s) if x != v), n)
            for v in range(s)]

def build_sigvars(VV, s):
    sigvars = [dict() for _ in range(s)]
    for i in range(s):
        for idx, vv in enumerate(VV[i]):
            key = (vv['order'], tuple(sorted(vv['bits'].items())))
            sigvars[i].setdefault(key, []).append(idx)
    return sigvars

def consistent(sig_choice, reps, s, i, j):
    """Edge (i,j) side consistency for all third vertices."""
    ri, rj = reps[i][sig_choice[i]], reps[j][sig_choice[j]]
    for k in range(s):
        if k == i or k == j:
            continue
        if ri['side'][(j, k)] != -rj['side'][(i, k)]:
            return False
    return True

def gen_cases(ks, n, s, VV=None, sigvars=None, max_leaves=None):
    if VV is None:
        VV = build_VV(ks, n, s)
    if sigvars is None:
        sigvars = build_sigvars(VV, s)
    reps = [{k: VV[i][idxs[0]] for k, idxs in sv.items()}
            for i, sv in enumerate(sigvars)]
    keys = [list(sv) for sv in sigvars]
    sig_choice = [None] * s
    sol = [None] * s
    tris = [tuple(t) for t in combinations(range(s), 3)]
    tris_by_v = [[] for _ in range(s)]
    for t in tris:
        tris_by_v[max(t)].append(t)
    state = {'leaves': 0}

    def leaf_bt(v):
        if v == s:
            yield [dict(x) for x in sol], tuple(idxs), \
                tuple(sig_choice)
            return
        for idx in sigvars[v][sig_choice[v]]:
            sol[v] = VV[v][idx]
            idxs[v] = idx
            if all(gm.tri_maybe(t, sol, n)
                   for t in tris_by_v[v]):
                yield from leaf_bt(v + 1)
        sol[v] = None

    idxs = [None] * s
    # wrap leaf generator for counting / cap
    def leaf_run():
        for out in leaf_bt(0):
            state['leaves'] += 1
            yield out

    def sig_run(v):
        for k in keys[v]:
            sig_choice[v] = k
            if all(consistent(sig_choice, reps, s, v, u)
                   for u in range(v)):
                if v == s - 1:
                    yield from leaf_run()
                else:
                    yield from sig_run(v + 1)
            if max_leaves and state['leaves'] > max_leaves:
                return
        sig_choice[v] = None

    yield from sig_run(0)
