#!/usr/bin/env python3
# tools/template_cert.py — template-synthesized certificates.
#
# For each leaf skeleton, enumerate anchored chain candidates
# x_0..x_{L+1} (consecutive segment of order[x_0]) and synthesize
# the multiplier assignment of the two wired chain families:
#
#   variant A ("interior right fan"): fans {x_0, x_L},
#     triangles Delta(x_0, x_j, x_{j+1}) for j = 1..L-1,
#     demand angles angle(x_{j-1}, x_j, x_{j+1}) for j = 1..L.
#     (This is the shape signed_chain_cert proves.)
#
#   variant B ("endpoint right fan"): fans {x_0, x_{L+1}},
#     triangles Delta(x_0, x_j, x_{j+1}) for j = 1..L,
#     demand angles angle(x_{j-1}, x_j, x_{j+1}) for j = 1..L.
#     (leaf_0046's saved certificate has this shape.)
#
# The synthesized multipliers are run through the SAME strict
# verify_cert as replay_cert (rnn/rle auto-elimination of leftover
# residual variables), so a hit means an actual certificate
# C - alpha*delta <= 0 with C >= alpha*tau — no bit guessing.
#
# usage: python tools/template_cert.py <certs_dir> [...]

import ast
import glob
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))

from fractions import Fraction as F
import generic_model as gm
from overfull_cert import verify_cert, CertError
from replay_cert import rebuild_orig


def orig_ids():
    """(kind, key) -> orig_id for the currently rebuilt ORIG."""
    ids = {}
    for cid, con in enumerate(gm.ORIG):
        ids[(con.kind, con.key)] = cid
    return ids


def ang_id(ids, apex, u, v):
    for key in ((apex, u, v), (apex, v, u),
                (apex, min(u, v), max(u, v))):
        cid = ids.get(('ang', key))
        if cid is not None:
            return cid
    return None


def is_demand_ang(con):
    """The usable demand bound: form `1 - r_{i,g} <= 0`
    (i.e. the complement arc carries at least one lambda cell)."""
    return (con.form.get(gm.CONST) == F(1)
            and gm.DELTA not in con.form
            and len(con.form) == 2
            and all(v == F(-1) for k, v in con.form.items()
                    if k != gm.CONST))


def is_arc_cap_ang(con):
    """The closing bound: form `sum of r's - delta + c <= 0`
    (an upper bound on a multi-gap arc — the `arc` branch of the
    legality bound angle <= pi - lam; the row-dependent constant c
    is whatever the skeleton gives, verify_cert does the ledger)."""
    return (con.form.get(gm.DELTA) == F(-1)
            and all(v == F(1) for k, v in con.form.items()
                    if k not in (gm.CONST, gm.DELTA)))


def synth_chain(d, ids, i0, p, L, variant):
    """Synthesize the chain-template multipliers at (i0, p, L).
    variant 'A': second fan at x_L, tris j=1..L-1.
    variant 'B': second fan at x_{L+1}, tris j=1..L.
    Returns (alpha, C, chain) or None."""
    s = d['s']
    skel = {e['v']: e for e in d['skeleton']}
    oi0 = skel[i0]['order']
    ln = len(oi0)
    if L > ln - 1:
        return None
    x = [i0] + [oi0[(p + j) % ln] for j in range(L + 1)]
    if len(set(x)) != L + 2:
        return None
    v1 = x[L] if variant == 'A' else x[L + 1]
    f0 = ids.get(('fan', i0))
    f1 = ids.get(('fan', v1))
    if f0 is None:
        return None
    if f0 is None or f1 is None:
        return None
    W = {f0: F(1)}
    if variant == 'C':
        # right closure by the legality bound angle(x0,x_{L+1},x_L)
        cid = ang_id(ids, x[L + 1], i0, x[L])
        if cid is None or not is_arc_cap_ang(gm.ORIG[cid]):
            return None
        W[cid] = F(1)
    else:
        if f1 is None:
            return None
        W[f1] = F(1)
    jmax = L - 1 if variant == 'A' else L
    for j in range(1, jmax + 1):
        cid = ids.get(('tri', (i0, x[j], x[j + 1])))
        if cid is None:
            return None
        W[cid] = W.get(cid, F(0)) - 1
    for j in range(1, L + 1):
        cid = ang_id(ids, x[j], x[j - 1], x[j + 1])
        if cid is not None and is_demand_ang(gm.ORIG[cid]):
            W[cid] = W.get(cid, F(0)) + 1
    try:
        alpha, C, _ = verify_cert(W, F(0))
    except CertError:
        return None
    return alpha, C, x


def scan_dir(dpath, verbose=False):
    leaves = covered = 0
    tot = {'A': 0, 'B': 0, 'C': 0}
    met_by = {'A': set(), 'B': set(), 'C': set()}
    for f in sorted(glob.glob(os.path.join(dpath, 'leaf_*.json'))):
        leaf = json.load(open(f, encoding='utf-8'))
        leaves += 1
        tau = F(str(leaf['target_tau']))
        rebuild_orig(leaf)
        ids = orig_ids()
        met = set()
        best = {}
        for i0 in range(leaf['s']):
            ln = len(leaf['skeleton'][i0]['order'])
            for p in range(ln):
                for L in range(2, ln):
                    for var in 'ABC':
                        r = synth_chain(leaf, ids, i0, p, L, var)
                        if r is None:
                            continue
                        alpha, C, x = r
                        tot[var] += 1
                        if C >= alpha * tau:
                            met.add(var)
                            if var not in best or C / alpha > best[var][0]:
                                best[var] = (C / alpha, x, L)
        if met:
            covered += 1
            for v in met:
                met_by[v].add(os.path.basename(f))
            if verbose:
                print(f'{os.path.basename(f)}: met by {sorted(met)} '
                      + ' '.join(f'{v}={best[v]}' for v in met))
    print(f'{dpath}: leaves={leaves} tau-covered={covered} '
          f'byA={len(met_by["A"])} byB={len(met_by["B"])} '
          f'byC={len(met_by["C"])} '
          f'valid-chains A={tot["A"]} B={tot["B"]} C={tot["C"]}')
    return covered, leaves


if __name__ == '__main__':
    for d in sys.argv[1:]:
        scan_dir(d)
