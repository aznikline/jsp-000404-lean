#!/usr/bin/env python3
# tools/certb_witness.py — emit replayable witnesses for certB hits.
#
# For each leaf:
#   1. scan_leaf finds certB hypothesis bundles (side-decoded);
#   2. the best-sigma bundle is synthesized as variant-B multipliers
#      (fan x0 + fan x_{L+1} + (-tri) per piece + demand angs) and run
#      through the independent verify_cert — no LP, exact rationals;
#   3. the witness record carries every field needed to re-check the
#      hit and to map it onto signed_chain_certB's premises.
#
# Levels:  RAW_HIT (bundle found) -> HYPOTHESES_CHECKED (sigma >= 2*tau)
#          -> CERT_REPLAYED (verify_cert proves C - alpha*delta <= 0
#          with C >= alpha*tau).
#
# usage: python tools/certb_witness.py DIR OUT.jsonl

import hashlib
import json
import os
import sys

from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import generic_model as gm
from overfull_cert import verify_cert, CertError
from replay_cert import rebuild_orig
from template_cert import (orig_ids, ang_id, is_demand_ang,
                           is_arc_cap_ang)
from certb_scan import scan_leaf, side_of, arc_qs, pos_map


def synth_certb(d, ids, hit):
    """certB multiplier set for one hypothesis bundle.

    The two boundary slots are independent topologies:
      fan_e — the endpoint fan equality; the boundary arc appears as
              the fan remainder and carries its qs baseline;
      cap_e — the angle-cap ∠ ≤ π−λ on the span arc
              (∠(x1,x0,x_{L+1}) at the left, ∠(x0,x_{L+1},x_L) at the
              right) realizing exactly one boundary cell.  Cap and fan
              at the same end DOUBLE-COUNT and must not both be used.
    Pieces: tri(x0,x_j,x_{j+1}) ×(−1), demand angs ×(+1) on the
    complement branch (is_demand_ang filters the correct form)."""
    sigma, i0, p, L, x, a, b, ms = hit
    f0 = ids.get(('fan', i0))
    f1 = ids.get(('fan', x[L + 1]))
    cap_a = ang_id(ids, i0, x[1], x[L + 1])
    if cap_a is not None and not is_arc_cap_ang(gm.ORIG[cap_a]):
        cap_a = None
    cap_b = ang_id(ids, x[L + 1], i0, x[L])
    if cap_b is not None and not is_arc_cap_ang(gm.ORIG[cap_b]):
        cap_b = None
    opts_a = ([('fan', f0)] if f0 is not None else []) + \
             ([('cap', cap_a)] if cap_a is not None else [])
    opts_b = ([('fan', f1)] if f1 is not None else []) + \
             ([('cap', cap_b)] if cap_b is not None else [])
    if not opts_a or not opts_b:
        return None
    dem = []
    for j in range(1, L + 1):
        cid = ang_id(ids, x[j], x[j - 1], x[j + 1])
        if cid is not None and is_demand_ang(gm.ORIG[cid]):
            dem.append(cid)
    best = None
    for ka, ca in opts_a:
        for kb, cb in opts_b:
            W = {ca: F(1), cb: F(1)}
            bad = False
            for j in range(1, L + 1):
                cid = ids.get(('tri', (i0, x[j], x[j + 1])))
                if cid is None:
                    bad = True
                    break
                W[cid] = W.get(cid, F(0)) - 1
            if bad:
                continue
            for cid in dem:
                W[cid] = W.get(cid, F(0)) + 1
            try:
                alpha, C, W_full = verify_cert(W, F(0))
            except CertError:
                continue
            if alpha <= 0:
                continue
            if best is None or C / alpha > best[1] / best[0]:
                best = (alpha, C, W, W_full, (ka, kb))
    return best


def gap_range(skel_row, u, v):
    """Gap indices of the forward arc u -> v in this row's order."""
    order = skel_row['order']
    pm = pos_map(order)
    pu, pv = pm[u], pm[v]
    ln = len(order)
    out, k = [], pu
    while k != pv:
        out.append(k)
        k = (k + 1) % ln
    return out


def skel_hash(d):
    blob = json.dumps(d['skeleton'], sort_keys=True).encode()
    return hashlib.sha256(blob).hexdigest()[:16]


def witness_for(d, hit, ids):
    """Build the witness record for one hypothesis-bundle hit.
    hit = (sigma, i0, p, L, x, a, b, ms)."""
    sigma, i0, p, L, x, a, b, ms = hit
    skel = {e['v']: e for e in d['skeleton']}
    pieces = []
    for j in range(1, L + 1):
        xj, xjm, xjp = x[j], x[j - 1], x[j + 1]
        demand_side = side_of(skel[xj], xjm, xjp)
        pieces.append({
            'j': j,
            'tri': [i0, xj, xjp],
            'hbA_side': side_of(skel[i0], xj, xjp),
            'hbT_side': side_of(skel[xj], i0, xjp),
            'hbS_side': side_of(skel[xjp], i0, xj),
            'hsplit': (j < 2) or (
                (pos_map(skel[xj]['order'])[xjm]
                 - pos_map(skel[xj]['order'])[i0])
                % len(skel[xj]['order'])
                <= (pos_map(skel[xj]['order'])[xjp]
                    - pos_map(skel[xj]['order'])[i0])
                % len(skel[xj]['order'])),
            'D_j_gaps': gap_range(skel[xj], xjm, xjp),
            'D_j_qs_baseline': arc_qs(skel[xj], xjm, xjp),
            'demand_side': demand_side,
            'm_j': ms[j - 1],
            'm_j_source': ('qs+complement_cap' if demand_side == -1
                           else 'qs_baseline'),
        })
    rec = {
        'chain': x, 'L': L, 'cut_p': p,
        'pieces': pieces,
        'H0': {'arc': [x[L + 1], x[1]], 'row': i0,
               'gaps': gap_range(skel[i0], x[L + 1], x[1]),
               'qs': arc_qs(skel[i0], x[L + 1], x[1]),
               'cap_side': side_of(skel[i0], x[1], x[L + 1]),
               'bound': a},
        'Hright': {'arc': [x[L], i0], 'row': x[L + 1],
                   'gaps': gap_range(skel[x[L + 1]], x[L], i0),
                   'qs': arc_qs(skel[x[L + 1]], x[L], i0),
                   'cap_side': side_of(skel[x[L + 1]], i0, x[L]),
                   'bound': b},
        'sigma': sigma,
        'premise_map': 'signed_chain_certB: hfanL=row(x0) tiling, '
                       'hcomp=row(x_{L+1}) halves, hsplit/hbA/hbT/hbS '
                       'per piece, hmD=m_j, hH0=a, hHL=b',
    }
    return rec


def main():
    dpath, out_path = sys.argv[1], sys.argv[2]
    stats = {'RAW_HIT': 0, 'HYPOTHESES_CHECKED': 0,
             'CERT_REPLAYED': 0, 'UNCLASSIFIED': 0, 'REJECTED': 0}
    with open(out_path, 'w', encoding='utf-8') as out:
        for f in sorted(os.listdir(dpath)):
            if not f.startswith('leaf_'):
                continue
            d = json.load(open(os.path.join(dpath, f), encoding='utf-8'))
            tau = F(str(d['target_tau']))
            hits = scan_leaf(d)
            if not hits:
                stats['UNCLASSIFIED'] += 1
                continue
            stats['RAW_HIT'] += 1
            good = [h for h in hits if h[0] >= 2 * tau]
            if not good:
                stats['UNCLASSIFIED'] += 1
                continue
            stats['HYPOTHESES_CHECKED'] += 1
            # try replaying the best few bundles (bounded)
            good.sort(key=lambda h: -h[0])
            played = None
            rebuild_orig(d)
            ids = orig_ids()
            for h in good[:8]:
                r = synth_certb(d, ids, h)
                if r is None:
                    continue
                alpha, C, W, W_full, topo = r
                if C >= alpha * tau:
                    played = (h, alpha, C, W, topo)
                    break
            if played is None:
                stats['REJECTED'] += 1
                continue
            stats['CERT_REPLAYED'] += 1
            (h, alpha, C, W, topo) = played
            w = witness_for(d, h, ids)
            w.update({
                'leaf': f, 'skel_sha256_16': skel_hash(d),
                'n': d['n'], 'tau': str(tau),
                'eliminated': f'{C} - {alpha}*delta <= 0',
                'alpha': str(alpha), 'C': str(C),
                'multipliers': {str(k): str(v) for k, v in W.items()},
                'boundary_topology': list(topo),
                'relaxation': 'closed (delta<=1 model)',
            })
            out.write(json.dumps(w) + '\n')
    print(dpath, stats)


if __name__ == '__main__':
    main()
