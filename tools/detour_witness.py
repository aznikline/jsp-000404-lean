#!/usr/bin/env python3
"""Detour-family witness recognizer.

The mixed-sign support family: fans at two rows u, a plus the signed
triangle pair +tri(w,u,x), -tri(w,u,a) sharing edge (w,u) implement the
detour identity

    dirArc(u;a,x) + dirArc(a;w,u) = dirArc(w;a,x) + angle(w,x,u)

so that 2pi = (fan_u - arc(u;a,x)) + (fan_a - arc(a;w,u))
             + dirArc(w;a,x) + angle(w,x,u).

Recognizes leaves by enumerating (u,a,w,x) quadruples, building the
canonical multipliers, and greedily adding demand-form angle bounds
(`sum r >= 1`, i.e. complement arcs >= lam).  Every hit is re-verified
by verify_cert -- no trust in the generator.

Usage: detour_witness.py <cert_dir> <out.jsonl>
"""
import json, glob, os, sys
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import generic_model as gm
from replay_cert import rebuild_orig
from template_cert import orig_ids
from overfull_cert import verify_cert, CertError


def demand_angs(ids, rows):
    """All ang constraints of demand shape (`c>=1`, all r coeffs -1,
    no delta) whose r-vars sit on the given rows."""
    out = []
    for (kind, key), cid in ids.items():
        if kind != 'ang':
            continue
        con = gm.ORIG[cid]
        if gm.DELTA in con.form:
            continue
        if con.form.get(gm.CONST, F(0)) < 1:
            continue
        if not all(v == F(-1) for k, v in con.form.items()
                   if k != gm.CONST):
            continue
        rws = {k[1] for k in con.form if k != gm.CONST}
        if rws and rws <= set(rows):
            out.append(cid)
    return out


def synth_detour(d, ids, u, a, w, x, tau):
    fu, fa = ids.get(('fan', u)), ids.get(('fan', a))
    twx = ids.get(('tri', (w, u, x)))
    twa = ids.get(('tri', (w, u, a)))
    if None in (fu, fa, twx, twa):
        return None
    W = {fu: F(1), fa: F(1), twx: F(1), twa: F(-1)}
    try:
        alpha, C, Wf = verify_cert(W, F(0))
    except CertError:
        return None
    used = set(W)
    if alpha <= 0:
        return None
    if C >= alpha * tau:
        return alpha, C, W, Wf, []
    # greedy demand-angle augmentation, bounded
    for _ in range(8):
        best = None
        for cid in demand_angs(ids, (u, a)):
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
            return alpha, C, W, Wf, sorted(used - {fu, fa, twx, twa})
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
        s = leaf['s']
        got = None
        for u in range(s):
            for a in range(s):
                if a == u:
                    continue
                for w in range(s):
                    if w in (u, a):
                        continue
                    for x in range(s):
                        if x in (u, a, w):
                            continue
                        stats['CANDIDATES'] += 1
                        r = synth_detour(leaf, ids, u, a, w, x, tau)
                        if r is not None:
                            got = (u, a, w, x, r)
                            break
                    if got: break
                if got: break
            if got: break
        if got is None:
            stats['REJECTED'] += 1
            continue
        stats['CERT_REPLAYED'] += 1
        u, a, w, x, (alpha, C, W, Wf, dems) = got
        recs.append(dict(
            leaf=os.path.basename(f), family='detour',
            u=u, a=a, w=w, x=x, tau=str(tau),
            alpha=str(alpha), C=str(C),
            multipliers={str(k): str(v) for k, v in W.items()},
            demand_angs=dems,
            eliminated=str(Wf.get('form', '')),
        ))
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, 'w', encoding='utf-8') as fh:
        for r in recs:
            fh.write(json.dumps(r) + '\n')
    print(dpath, stats)


if __name__ == '__main__':
    main()
