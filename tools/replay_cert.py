#!/usr/bin/env python3
"""replay_cert.py — offline replay + template classification of the
saved certificate evidence files produced by `overfull_cert.py --save`.

No LP solver is invoked.  For every leaf JSON we

  1. rebuild the vertex skeletons (order/bits/qs -> gaps/arcs/angles)
     and regenerate the ORIG constraint list deterministically;
  2. integrity-check each saved constraint form against the rebuilt
     ORIG entry (same orig_id must carry the same form/is_eq);
  3. re-verify the saved multipliers with the strict
     `overfull_cert.verify_cert` at the saved target tau;
  4. classify the certificate shape:

       fat-arc   — some vertex i has a same-bit pair (u,v) whose fan
                   arc carries >= n integer cells; the single
                   `ang(i,u,v)` bound + rnn eliminations already prove
                   delta >= tau.  (Lean: arc_overflow_geometric_of_cells)
       polygon   — the saved ang support is a full s-cycle
                   {(v_t, v_{t-1}, v_{t+1})}.  (Lean: cycle_cert —
                   the (t-2)pi angle sum is still an unproved premise)
       general-signed — anything else (signed triangle / fan /
                   remainder combination not matching the above).

The two named families are NOT assumed complete: leaves they cannot
explain land in `general-signed`, which is the interesting output.

Usage: replay_cert.py DIR [tau_num tau_den]
"""
import ast
import glob
import json
import sys
from fractions import Fraction as F
from itertools import combinations, permutations

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
sys.path.insert(0, 'tools')

import generic_model as gm
from overfull_cert import verify_cert, CertError

ZERO, ONE = F(0), F(1)
CONST, DELTA = gm.CONST, gm.DELTA


def variant_from_record(v, others, n):
    """Rebuild one variant dict from saved (order, bits, qs).

    Replicates the computation inside generic_model.vertex_variants
    for a single tuple; the skeleton fields (order/bits/qs) come from
    the evidence file, everything else is derived."""
    order = list(v['order'])
    bits = {int(k): b for k, b in v['bits'].items()}
    qs = list(v['qs'])
    vi = v['v']
    m = len(others)
    pos = {d: t for t, d in enumerate(order)}
    gaps = [gm.add(gm.mk(qs[t]), gm.var(('r', vi, t)))
            for t in range(m)]

    def arc(a, b):
        e = gm.mk(0)
        for t in range(min(a, b), max(a, b)):
            e = gm.add(e, gaps[t])
        return e

    arcs, angles, side = {}, {}, {}
    for u, w in combinations(others, 2):
        a_ = arc(pos[u], pos[w])
        arcs[frozenset((u, w))] = a_
        if bits[u] == bits[w]:
            angles[frozenset((u, w))] = a_
        else:
            angles[frozenset((u, w))] = gm.add(
                gm.add(gm.mk(n), gm.var(DELTA)), a_, -ONE)
    for j in others:
        for k in others:
            if k == j:
                continue
            sgn = 1 if pos[k] > pos[j] else -1
            if bits[k] != bits[j]:
                sgn = -sgn
            side[(j, k)] = sgn
    return dict(v=vi, order=order, bits=bits, qs=qs,
                gaps=gaps, arcs=arcs, angles=angles, side=side)


def rebuild_orig(rec):
    n, s = rec['n'], rec['s']
    vs = []
    for v in rec['skeleton']:
        others = [x for x in range(s) if x != v['v']]
        vs.append(variant_from_record(v, others, n))
    gm.ORIG.clear()
    b = gm.build_case(vs, n, 'A')
    assert b is not None
    return vs


def integrity_check(rec):
    """Saved forms must equal the rebuilt ORIG forms."""
    bad = []
    for c in rec['constraints']:
        cid = c['orig_id']
        con = gm.ORIG[cid]
        if con.is_eq != c['is_eq'] or con.kind != c['kind']:
            bad.append((cid, 'kind/is_eq mismatch'))
            continue
        rebuilt = {str(k): str(x) for k, x in con.form.items()}
        if rebuilt != c['form']:
            bad.append((cid, 'form mismatch'))
    return bad


def saved_W(rec):
    return {c['orig_id']: F(c['multiplier'])
            for c in rec['constraints'] if F(c['multiplier']) != 0}


def fat_arc_hit(rec, n, tau):
    """Find a same-bit arc with >= n cells; verify the mini-certificate
    {ang(i,u,v): 1} end-to-end through the strict verifier."""
    s = rec['s']
    for v in rec['skeleton']:
        i, order = v['v'], v['order']
        bits = {int(k): b for k, b in v['bits'].items()}
        qs, pos = v['qs'], {d: t for t, d in enumerate(order)}
        for u, w in combinations([x for x in range(s) if x != i], 2):
            if bits[u] != bits[w]:
                continue
            lo, hi = min(pos[u], pos[w]), max(pos[u], pos[w])
            cells = sum(qs[lo:hi])
            if cells < n:
                continue
            cid = next((k for k, c in enumerate(gm.ORIG)
                        if c.kind == 'ang'
                        and c.key == (i, u, w)), None)
            if cid is None:
                continue
            try:
                a_, C_, _ = verify_cert({cid: ONE}, tau)
            except CertError:
                continue
            if C_ >= a_ * tau:
                return (i, u, w, cells, str(C_ / a_))
    return None


def polygon_hit(rec):
    """Does the saved ang support form a full s-cycle?"""
    s = rec['s']
    keys = [(c['orig_id'], ast.literal_eval(c['key']))
            for c in rec['constraints']
            if c['kind'] == 'ang' and F(c['multiplier']) > 0]
    if len(keys) != s or len({k[1][0] for k in keys}) != s:
        return None
    pairs = {k[1][0]: frozenset(k[1][1:]) for k in keys}
    for perm in permutations(range(1, s)):
        v = (0,) + perm
        if all(pairs[v[t]] == frozenset((v[(t - 1) % s],
                                         v[(t + 1) % s]))
               for t in range(s)):
            return v
    return None


def replay_dir(d, tau):
    rows = []
    counts = {'fat-arc': 0, 'polygon': 0, 'general-signed': 0,
              'VERIFY-FAIL': 0, 'INTEGRITY-FAIL': 0}
    for path in sorted(glob.glob(f'{d}/leaf_*.json')):
        rec = json.load(open(path, encoding='utf-8'))
        tag = path.split('\\')[-1].split('/')[-1]
        rebuild_orig(rec)
        bad = integrity_check(rec)
        if bad:
            counts['INTEGRITY-FAIL'] += 1
            rows.append((tag, 'INTEGRITY-FAIL', str(bad[:2])))
            continue
        try:
            a_, C_, _ = verify_cert(saved_W(rec), F(rec['target_tau']))
            ok = C_ >= a_ * tau
        except CertError as e:
            counts['VERIFY-FAIL'] += 1
            rows.append((tag, 'VERIFY-FAIL', str(e)))
            continue
        if not ok:
            counts['VERIFY-FAIL'] += 1
            rows.append((tag, 'VERIFY-FAIL',
                         f'proven {C_ / a_} < tau {tau}'))
            continue
        fa = fat_arc_hit(rec, rec['n'], tau)
        if fa:
            counts['fat-arc'] += 1
            rows.append((tag, 'fat-arc',
                         f'V{fa[0]} arc {fa[1]}->{fa[2]} '
                         f'cells={fa[3]} cert d>={fa[4]}'))
            continue
        pg = polygon_hit(rec)
        if pg:
            counts['polygon'] += 1
            rows.append((tag, 'polygon', f'cycle {pg}'))
            continue
        counts['general-signed'] += 1
        rows.append((tag, 'general-signed', ''))
    for r in rows:
        print(f'  {r[0]}: {r[1]}  {r[2]}')
    print(f'== classification: {counts}')
    print(f'== total leaves replayed: {len(rows)} (offline, no LP)')


if __name__ == '__main__':
    d = sys.argv[1]
    tau = F(int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else F(1, 2)
    replay_dir(d, tau)
