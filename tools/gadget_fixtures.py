#!/usr/bin/env python3
"""gadget_fixtures.py — export representative link_graph gadgets.

Emits tools/gadget_fixtures.json: gadgets in the exact field layout of
the Lean `Gadget` structure (Jsp000404/Gadget.lean):

    fans    : v -> ±1          (fan equality weights; 0 omitted)
    links   : [a, b, h, σ]     (σ · Δ{a,b,h} triangle links)
    charges : [v, a, b]        (complementary ∠v{a,b} ≥-style gains)
    caps    : {v, kind, a, b, gap, m}
              kind 'rle'   : r_gap ≤ 1,          range {gap},  B=1,       u=0
              kind 'piLam' : direct ∠v{a,b} bound, range arc,   B=n-1-q,   u=1
              kind 'nn'    : compl.  ∠v{a,b} ≥ 0,  range arc,   B=n-q,     u=1

plus the derived residual bookkeeping exactly as link_graph computes
it (coef/dco/con → c = -dco, C = -con, K, Bcap, u, bound, score=2·bound).

The generator replays eval_chain / pure_gadget from link_graph.py with
the identical selection logic, but also records WHICH charge arcs and
cap options were chosen (link_graph only keeps the scalar totals).

Usage:  python3 gadget_fixtures.py [--records K]
"""
import sys, json, itertools
sys.path.insert(0, '.')
from fractions import Fraction as F
import skeleton_enum as sen
import link_graph as lg

ZERO = F(0)


def eval_chain_full(ctx, h, edges, fans):
    """eval_chain + explicit charge/cap choices (same selection logic)."""
    n, s = ctx.n, ctx.s
    R = {}
    con = ZERO
    dc = 0
    for v, fw in fans.items():
        Rd, cc, dd = ctx.fan[(v, fw)]
        for k, t in Rd.items():
            R[k] = R.get(k, 0) + t
        con += cc
        dc += dd
    for a, b, sig in edges:
        Rd, cc, dd = ctx.link[(min(a, b), max(a, b), h, sig)]
        for k, t in Rd.items():
            R[k] = R.get(k, 0) + t
        con += cc
        dc += dd
    c = -dc
    C = -con
    K = ZERO
    charges = []
    capvars = []
    for v in range(s):
        blk = {g: R.get((v, g), 0) for g in range(s - 1)}
        blk = {g: k for g, k in blk.items() if k != 0}
        if not blk:
            continue
        posblk = {g: k for g, k in blk.items() if k > 0}
        negblk = {g: -k for g, k in blk.items() if k < 0}
        if posblk:
            pset = frozenset(posblk)
            cand = []
            for (a, b), (comp, rng, q) in ctx.ang[v].items():
                if comp and rng <= pset:
                    gain = min(posblk[g] for g in rng) * (F(1) - q)
                    if gain > 0:
                        cand.append((gain, rng, a, b))
            cand.sort(key=lambda t: -t[0])
            used = frozenset()
            for gain, rng, a, b in cand:
                if not (rng & used):
                    K += gain
                    used |= rng
                    charges.append({'v': v, 'a': a, 'b': b,
                                    'gain': str(gain)})
        if negblk:
            vopts = []
            mmax = max(negblk.values())
            nset = frozenset(negblk)
            for (a, b), (comp, rng, q) in ctx.ang[v].items():
                if not comp and nset <= rng:
                    caps = [{'v': v, 'kind': 'piLam', 'a': a, 'b': b,
                             'gap': 0, 'm': int(mmax)}]
                    vopts.append((mmax * (F(n - 1) - q), F(mmax), caps))
            varopts = []
            for g, m_ in negblk.items():
                chs = [(F(m_), ZERO,
                        [{'v': v, 'kind': 'rle', 'a': 0, 'b': 0,
                          'gap': g, 'm': int(m_)}])]
                best_cap = None
                for (a, b), (comp, rng, q) in ctx.ang[v].items():
                    if not comp and g in rng:
                        cand2 = F(n - 1) - q
                        if best_cap is None or cand2 < best_cap[0]:
                            best_cap = (cand2, a, b)
                if best_cap is not None:
                    chs.append((m_ * best_cap[0], F(m_),
                                [{'v': v, 'kind': 'piLam',
                                  'a': best_cap[1], 'b': best_cap[2],
                                  'gap': 0, 'm': int(m_)}]))
                varopts.append(chs)
            for combo in itertools.product(*varopts):
                vopts.append((sum(t[0] for t in combo),
                              sum(t[1] for t in combo),
                              [cp for t in combo for cp in t[2]]))
            keep = []
            for t in vopts:
                if not any(o[0] <= t[0] and o[1] <= t[1]
                           and (o[0], o[1]) != (t[0], t[1])
                           for o in vopts):
                    keep.append(t)
            capvars.append(keep)
    c = F(c)
    best = None
    for combo in itertools.product(*capvars) if capvars else [()]:
        Bcap = sum(t[0] for t in combo)
        u = sum(t[1] for t in combo)
        if c + u <= 0:
            continue
        bound = (K - Bcap - C) / (c + u)
        if best is None or bound > best[0]:
            best = (bound, Bcap, u,
                    [cp for t in combo for cp in t[2]])
    if best is None:
        return None
    bound, Bcap, u, caps = best
    return {'pivot': h,
            'links': [[a, b, h, sig] for a, b, sig in edges],
            'fans': {str(v): int(t) for v, t in sorted(fans.items())},
            'charges': charges, 'caps': caps,
            'coef': {f'{v},{g}': int(t)
                     for (v, g), t in sorted(R.items()) if t != 0},
            'c': str(c), 'u': str(u), 'C': str(C), 'K': str(K),
            'Bcap': str(Bcap), 'bound': str(bound),
            'score': str(2 * bound), 'pure': False}


def pure_gadget_full(ctx):
    """pure_gadget + explicit cap entries (same selection logic)."""
    n, s = ctx.n, ctx.s
    cand = []
    for v in range(s):
        for (a, b), (comp, rng, q) in ctx.ang[v].items():
            if not comp and q >= n:
                cand.append((F(q - (n - 1)), v, rng, a, b))
    if not cand:
        return None
    best = None
    for m in range(1, len(cand) + 1):
        for sel in itertools.combinations(cand, m):
            ok = True
            for i in range(len(sel)):
                for j in range(i + 1, len(sel)):
                    if sel[i][1] == sel[j][1] and sel[i][2] & sel[j][2]:
                        ok = False
            if not ok:
                continue
            bnd = sum(t[0] for t in sel) / m
            if best is None or bnd > best[0]:
                best = (bnd, sel)
    if best is None:
        return None
    bnd, sel = best
    caps = [{'v': v, 'kind': 'piLam', 'a': a, 'b': b, 'gap': 0, 'm': 1}
            for _, v, _, a, b in sel]
    return {'pivot': None, 'links': [], 'fans': {},
            'charges': [], 'caps': caps, 'coef': {},
            'c': '0', 'u': str(F(len(sel))), 'C': '0', 'K': '0',
            'Bcap': str(-sum(t[0] for t in sel)),
            'bound': str(bnd), 'score': str(2 * bnd), 'pure': True}


def classify(rec):
    tags = set()
    if rec['pure']:
        tags.add('pure-cap')
    elif not rec['links']:
        tags.add('fan-only')
    else:
        tags.add('fan-strip')
    if any(v > 0 for v in rec['coef'].values()) and \
            any(v < 0 for v in rec['coef'].values()):
        tags.add('mixed-sign')
    b = F(rec['bound'])
    if b >= 1:
        tags.add('score2')
    elif b >= F(1, 2):
        tags.add('score1')
    else:
        tags.add('score0')
    return tags


def skel_json(sol, n, s):
    return {'n': n, 's': s,
            'vertices': [
                {'pos': {str(d): t for t, d in enumerate(vv['order'])},
                 'bits': {str(d): int(b) for d, b in vv['bits'].items()},
                 'q': [int(q) for q in vv['qs']]}
                for vv in sol]}


def synthetic_sol(qss):
    """Synthetic s=4 skeleton: trivial order/bits, given q tuples.
    All bits equal ⇒ every angle is direct (never complementary)."""
    sol = []
    for v in range(4):
        others = tuple(x for x in range(4) if x != v)
        sol.append({'order': others,
                    'bits': {d: 0 for d in others},
                    'qs': tuple(qss[v])})
    return sol


def main():
    K = int(sys.argv[sys.argv.index('--records') + 1]) \
        if '--records' in sys.argv else 43
    n = s = 4
    dd = json.load(open('chain_dump_s4.json'))[:K]
    VV = sen.build_VV((3, 2, 2, 1), n)
    out = []
    seen = set()
    want = {'pure-cap', 'fan-only', 'fan-strip', 'mixed-sign',
            'score0', 'score1', 'score2'}
    got = set()
    # synthetic skeletons: guaranteed pure-cap gadgets, incl. score ≥ 2
    for tag, qss in [
            ('syn-purecap', [(2, 2, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)]),
            ('syn-purecap2',
             [(3, 3, 0), (2, 2, 0), (0, 0, 0), (0, 0, 0)])]:
        sol = synthetic_sol(qss)
        ctx = lg.Ctx(sol, n, s)
        pg = pure_gadget_full(ctx)
        if pg is None:
            continue
        pg['skeleton'] = tag
        pg['tags'] = sorted(classify(pg))
        pg['skel'] = skel_json(sol, n, s)
        out.append(pg)
        got |= classify(pg)
    for rec in dd:
        sol = [VV[v][rec['idxs'][v]] for v in range(s)]
        ctx = lg.Ctx(sol, n, s)
        # always include the pure-cap gadget when it exists
        pg = pure_gadget_full(ctx)
        if pg is not None:
            key = json.dumps(pg, sort_keys=True)
            if key not in seen:
                seen.add(key)
                pg['skeleton'] = rec['tag']
                pg['tags'] = sorted(classify(pg))
                pg['skel'] = skel_json(sol, n, s)
                out.append(pg)
                got |= classify(pg)
        fas = list(lg.fan_assignments(s))
        local_best = None
        local_cov = []
        tag_count = {}
        for g in out:
            for t in g['tags']:
                tag_count[t] = tag_count.get(t, 0) + 1
        for h in range(s):
            outer = [v for v in range(s) if v != h]
            for r_ in range(0, len(outer) + 1):
                perms = [()] if r_ == 0 else \
                    itertools.permutations(outer, r_)
                for perm in perms:
                    for closed in (False, True):
                        for edges in lg.edge_lists(list(perm), closed):
                            for fa in fas:
                                res = eval_chain_full(ctx, h, edges, fa)
                                if res is None:
                                    continue
                                tags = classify(res)
                                if local_best is None or \
                                        F(res['bound']) > \
                                        F(local_best['bound']):
                                    local_best = res
                                if any(tag_count.get(t, 0) < 3
                                       for t in tags):
                                    local_cov.append(res)
                                    for t in tags:
                                        tag_count[t] = \
                                            tag_count.get(t, 0) + 1
        for res in [local_best] + local_cov:
            if res is None:
                continue
            key = json.dumps(
                {k: v for k, v in res.items()
                 if k not in ('skeleton', 'tags', 'skel')},
                sort_keys=True)
            if key in seen:
                continue
            seen.add(key)
            res['skeleton'] = rec['tag']
            res['tags'] = sorted(classify(res))
            res['skel'] = skel_json(sol, n, s)
            out.append(res)
            got |= classify(res)
        if got >= want and len(out) >= 28:
            break
    for i, g in enumerate(out):
        g['id'] = f'g{i:02d}'
    json.dump(out, open('gadget_fixtures.json', 'w'), indent=1)
    print(f'wrote {len(out)} gadgets; tags covered: {sorted(got)}')
    from collections import Counter
    cnt = Counter(t for g in out for t in g['tags'])
    print(dict(cnt))


if __name__ == '__main__':
    main()
