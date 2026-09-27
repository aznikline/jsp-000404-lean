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

       FAT_ARC_CERTIFIED   — some vertex i has a same-bit pair (u,v)
                   whose fan arc carries >= n integer cells; the single
                   `ang(i,u,v)` bound + rnn eliminations already prove
                   delta >= tau, verified end-to-end through the strict
                   verifier.  (Lean: arc_overflow_geometric_of_cells —
                   a genuinely proved certificate shape.)
       POLYGON_SUPPORT_MATCH — the saved ang support is a full s-cycle
                   {(v_t, v_{t-1}, v_{t+1})}.  This is only a SUPPORT
                   SHAPE match: the corresponding (t-2)pi angle sum is
                   still an unproved premise (Lean: cycle_cert needs
                   `hsum`), so the label records recognition, not a
                   completed geometric proof.
       UNCLASSIFIED_SIGNED_CERT — anything else: a signed fan/tri/
                   remainder combination not matching either recognizer.
                   NOT certified as DebtChain or any other named
                   structure; "not recognized" does not imply no
                   simpler certificate exists for the same leaf.

The recognizers are NOT assumed complete: unclassified leaves are the
interesting output, and a non-match says nothing about alternative
certificates for the same skeleton.

Exit status: 0 iff at least one record was replayed and every record
passed integrity + strict verification + derived-field consistency.
Any VERIFY-FAIL / INTEGRITY-FAIL / DERIVED-MISMATCH, a missing
directory, or zero matched records exits nonzero.

Usage: replay_cert.py DIR [tau_num tau_den]
"""
import ast
import glob
import json
import os
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


def derived_check(rec, alpha, C, W_full):
    """Compare the saved derived fields against the recomputation.

    `proven_bound` must equal C/alpha, `eliminated_form` must be the
    recomputed `C - alpha*delta <= 0`, and each constraint's saved
    `elim_weight` must equal W_full[cid] - multiplier."""
    bad = []
    if F(rec.get('proven_bound', '?')) != C / alpha:
        bad.append(('proven_bound',
                    f"saved {rec.get('proven_bound')} != "
                    f'recomputed {C / alpha}'))
    form = f'{C} - {alpha}*delta <= 0'
    if rec.get('eliminated_form') != form:
        bad.append(('eliminated_form',
                    f"saved {rec.get('eliminated_form')} != {form}"))
    for con in rec['constraints']:
        cid = con['orig_id']
        saved_elim = F(con.get('elim_weight', '0'))
        recomputed = W_full.get(cid, ZERO) - F(con['multiplier'])
        if saved_elim != recomputed:
            bad.append(('elim_weight',
                        f'orig_id={cid}: saved {saved_elim} != '
                        f'recomputed {recomputed}'))
    return bad


def replay_dir(d, tau):
    """Returns (counts, n_records)."""
    rows = []
    counts = {'FAT_ARC_CERTIFIED': 0, 'POLYGON_SUPPORT_MATCH': 0,
              'UNCLASSIFIED_SIGNED_CERT': 0,
              'VERIFY-FAIL': 0, 'INTEGRITY-FAIL': 0,
              'DERIVED-MISMATCH': 0}
    paths = sorted(glob.glob(f'{d}/leaf_*.json'))
    for path in paths:
        rec = json.load(open(path, encoding='utf-8'))
        tag = path.split('\\')[-1].split('/')[-1]
        rebuild_orig(rec)
        bad = integrity_check(rec)
        if bad:
            counts['INTEGRITY-FAIL'] += 1
            rows.append((tag, 'INTEGRITY-FAIL', str(bad[:2])))
            continue
        try:
            a_, C_, W_full = verify_cert(saved_W(rec),
                                         F(rec['target_tau']))
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
        dbad = derived_check(rec, a_, C_, W_full)
        if dbad:
            counts['DERIVED-MISMATCH'] += 1
            rows.append((tag, 'DERIVED-MISMATCH', str(dbad[:2])))
            continue
        fa = fat_arc_hit(rec, rec['n'], tau)
        if fa:
            counts['FAT_ARC_CERTIFIED'] += 1
            rows.append((tag, 'FAT_ARC_CERTIFIED',
                         f'V{fa[0]} arc {fa[1]}->{fa[2]} '
                         f'cells={fa[3]} cert d>={fa[4]}'))
            continue
        pg = polygon_hit(rec)
        if pg:
            counts['POLYGON_SUPPORT_MATCH'] += 1
            rows.append((tag, 'POLYGON_SUPPORT_MATCH',
                         f'cycle {pg}'))
            continue
        counts['UNCLASSIFIED_SIGNED_CERT'] += 1
        rows.append((tag, 'UNCLASSIFIED_SIGNED_CERT', ''))
    for r in rows:
        print(f'  {r[0]}: {r[1]}  {r[2]}')
    print(f'== classification: {counts}')
    print(f'== total leaves replayed: {len(rows)} (offline, no LP)')
    return counts, len(rows)


if __name__ == '__main__':
    d = sys.argv[1]
    tau = F(int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else F(1, 2)
    if not os.path.isdir(d):
        print(f'REPLAY-ERROR: directory {d} does not exist')
        sys.exit(2)
    counts, nrec = replay_dir(d, tau)
    if nrec == 0:
        print(f'REPLAY-ERROR: no leaf_*.json records under {d}')
        sys.exit(2)
    fails = (counts['VERIFY-FAIL'] + counts['INTEGRITY-FAIL']
             + counts['DERIVED-MISMATCH'])
    if fails:
        print(f'REPLAY-FAIL: {fails} records failed replay checks')
        sys.exit(1)
    sys.exit(0)
