#!/usr/bin/env python3
"""Single-fan transfer-family witness recognizer.

Two sub-families built on `dirArc_triangle_transfer` /
`detour_arc_compose` (Jsp000404/K3bGeometry.lean):

T1  single fan + one triangle transfer (leaf_0970 shape):
      W = {fan_u: +1, tri(v,u,w): s}   with s in {+1,-1};
      the triangle apex pattern must be (direct, complement, direct)
      so that  dirArc(u;v,w) = dirArc(v;u,w) + dirArc(w;v,u).

T2  single fan + double-detour composition (leaf_0968 shape):
      W = {fan_u1: +1,
           tri(w,u1,x): +1, tri(w,u1,a): -1,
           tri(w,u2,x): -1, tri(w,u2,a): +1}
      implementing  dirArc(u1;a,x) = dirArc(u2;a,x)
                    + (dirArc a w u2 - dirArc a w u1)
                    + (angle w x u1 - angle w x u2);
      negatively occurring arcs are absorbed by rle caps (r <= 1).

Demand-form angle bounds (sum r >= 1) and rle caps (r <= 1) are added
greedily when the base combination misses tau.  Every hit is
re-verified by verify_cert -- no trust in the generator.

Usage: transfer_witness.py <cert_dir> <out.jsonl>
"""
import json, glob, os, sys
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import generic_model as gm
from replay_cert import rebuild_orig
from template_cert import orig_ids
from overfull_cert import verify_cert, CertError


def extra_bounds(ids):
    """Demand angs (c>=1, all r coeffs -1) and rle caps (r<=1)."""
    angs, caps = [], []
    for (kind, key), cid in ids.items():
        con = gm.ORIG[cid]
        if gm.DELTA in con.form:
            continue
        rvars = {k: v for k, v in con.form.items() if k != gm.CONST}
        if kind == 'ang' and con.form.get(gm.CONST, F(0)) >= 1 \
                and all(v == F(-1) for v in rvars.values()):
            angs.append(cid)
        if kind == 'rle' and len(rvars) == 1 \
                and next(iter(rvars.values())) == F(1) \
                and con.form.get(gm.CONST, F(0)) == F(-1):
            caps.append(cid)
    return angs, caps


def augment(W, tau, ids):
    """Greedy demand/cap augmentation until C >= alpha*tau."""
    try:
        alpha, C, Wf = verify_cert(W, F(0))
    except CertError:
        return None
    if alpha <= 0:
        return None
    used = set(W)
    if C >= alpha * tau:
        return alpha, C, W, Wf
    angs, caps = extra_bounds(ids)
    for _ in range(10):
        best = None
        for cid in angs + caps:
            if cid in used:
                continue
            W2 = dict(W); W2[cid] = W2.get(cid, F(0)) + 1
            try:
                a2, C2, _ = verify_cert(W2, F(0))
            except CertError:
                continue
            if a2 > 0 and C2 / a2 > C / alpha:
                best = (cid, a2, C2, W2)
        if best is None:
            return None
        cid, alpha, C, W = best
        used.add(cid)
        if C >= alpha * tau:
            Wf = verify_cert(W, F(0))[2]
            return alpha, C, W, Wf
    return None


def synth_T1(d, ids, u, tau):
    """fan_u + one triangle containing u (both signs)."""
    fu = ids.get(('fan', u))
    if fu is None:
        return None
    for (kind, key), cid in ids.items():
        if kind != 'tri' or u not in key:
            continue
        for sgn in (F(1), F(-1)):
            r = augment({fu: F(1), cid: sgn}, tau, ids)
            if r is not None:
                return ('T1', (u, key, int(sgn)), r)
    return None


def synth_T2(d, ids, u1, tau):
    """fan_u1 + double detour through a shared anchor arc (w;a,x)."""
    fu = ids.get(('fan', u1))
    if fu is None:
        return None
    s = d['s']
    for w in range(s):
        if w == u1:
            continue
        for u2 in range(s):
            if u2 in (w, u1):
                continue
            for a in range(s):
                if a in (w, u1, u2):
                    continue
                for x in range(s):
                    if x in (w, u1, u2, a):
                        continue
                    t = [ids.get(('tri', (w, u1, x))),
                         ids.get(('tri', (w, u1, a))),
                         ids.get(('tri', (w, u2, x))),
                         ids.get(('tri', (w, u2, a)))]
                    if None in t:
                        continue
                    W = {fu: F(1), t[0]: F(1), t[1]: F(-1),
                         t[2]: F(-1), t[3]: F(1)}
                    r = augment(W, tau, ids)
                    if r is not None:
                        return ('T2', (u1, w, u2, a, x), r)
    return None


def main():
    dpath, out = sys.argv[1], sys.argv[2]
    stats = dict(CANDIDATES=0, CERT_REPLAYED=0, REJECTED=0)
    recs = []
    for f in sorted(glob.glob(os.path.join(dpath, 'leaf_*.json'))):
        leaf = json.load(open(f, encoding='utf-8'))
        tau = F(str(leaf['target_tau']))
        rebuild_orig(leaf)
        ids = orig_ids()
        got = None
        for u in range(leaf['s']):
            got = synth_T1(leaf, ids, u, tau)
            if got is None:
                got = synth_T2(leaf, ids, u, tau)
            if got is not None:
                break
        if got is None:
            stats['REJECTED'] += 1
            continue
        stats['CERT_REPLAYED'] += 1
        fam, params, (alpha, C, W, Wf) = got
        recs.append(dict(
            leaf=os.path.basename(f), family='transfer_' + fam,
            params=list(map(str, params)) if not isinstance(params[0], int)
                   else params, tau=str(tau),
            alpha=str(alpha), C=str(C),
            multipliers={str(k): str(v) for k, v in W.items()},
            eliminated=str(Wf.get('form', '')),
        ))
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, 'w', encoding='utf-8') as fh:
        for r in recs:
            fh.write(json.dumps(r) + '\n')
    print(dpath, stats)


if __name__ == '__main__':
    main()
