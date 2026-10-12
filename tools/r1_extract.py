#!/usr/bin/env python3
"""R1 terminal extraction: class-free multiset signatures, dual-solver DFS.

Model: build(P) from s7_canon (P non-anchor t-vars, chords d_ij i<j).
Row signatures: tools/r1_msig.py — gap-witness Ors over the row's chord
multiset (preds: None=bottom + each chord).

Each tree node carries meta to emit Lean:
  'tr'  ijk           -> rcases m.htr i j k
  'or'  (r, oi, ei)   -> rcases of oi-th signature Or of row r
  'sub' (and_, ei)    -> ei-th Or inside the pushed disjunct of node and_
  'term' core         -> linarith only [...]
"""
import z3, itertools, json, sys, time, os

sys.setrecursionlimit(500000)

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s7_canon import build, nb
from r1_msig import msig_ors


def disjs(e):
    return e.children() if z3.is_or(e) else [e]


def or_children(e):
    """Or-subterms inside a pushed disjunct (top two And levels)."""
    out = []
    chs = e.children() if z3.is_and(e) else [e]
    for ch in chs:
        if z3.is_or(ch):
            out.append(ch)
        elif z3.is_and(ch):
            out.extend(g for g in ch.children() if z3.is_or(g))
    return out


def linear_strip(dj):
    out = []
    chs = dj.children() if z3.is_and(dj) else [dj]
    for ch in chs:
        if z3.is_or(ch):
            continue
        if z3.is_and(ch) and any(z3.is_or(g) for g in ch.children()):
            continue
        if z3.is_and(ch):
            out.extend(g for g in ch.children() if not z3.is_or(g))
        else:
            out.append(ch)
    return out


def build_tree(P, spec, fixvec=None, budget_nodes=2_000_000,
               verbose=False):
    """spec = [(rank, kind)] kinds 's0'|'s1'|'s2'.

    fixvec: optional {r: {pred_index: (lo,hi)}} pinning each row's band
    vector as ground (band-vector decomposition).  preds indexed by
    position in [None] + S (0 = bottom gap)."""
    delta, t, d, D, p, base, trips = build(P)
    ground = [('hplo', delta >= 0), ('hphi', delta < 1),
              ('ht0b', t[0] >= 0), ('htPb', t[P - 1] <= delta)]
    for i in range(P - 1):
        ground.append((f'ht{i}{i+1}', t[i] < t[i + 1]))
    for i in range(P):
        for j in range(i + 1, P):
            ground.append((f'hc{i}{j}',
                           z3.And(t[i] + 1 <= d[(i, j)],
                                  d[(i, j)] <= p - 1 + t[j])))
    ors = {}          # name -> (typ, r, expr, emitmeta)
    row_ors = {}
    for (r, kind) in spec:
        S = [D(r, j) for j in range(P) if j != r]
        preds = [None] + list(S)
        for oi, (tag, pred, e) in enumerate(
                msig_ors(t[r], S, p, kind, rowtag=f'r{r}')):
            if tag in ('gb', 'gsum'):
                ground.append((f'gbr{r}o{oi}', e))
                continue
            if fixvec is not None and r in fixvec and tag != 'spd':
                # band-vector pinned: replace signature band/card ors
                continue
            nm = f'r{r}o{oi}'
            ors[nm] = ('or', r, e, (r, oi, tag))
            row_ors.setdefault(r, []).append(nm)
        if fixvec is not None and r in fixvec:
            from r1_msig import band as _band
            import z3 as _z3
            spv = {k: _z3.Real(f'sp_r{r}_{k}') for k in range(len(preds))}
            for k, (lo, hi) in fixvec[r].items():
                pr = preds[k]
                basepr = t[r] if pr is None else pr
                ground.append((f'bv{r}k{k}',
                               _band(spv[k], basepr, lo, hi)))
    for ij, tr in trips.items():
        ors[f'tr{ij[0]}{ij[1]}{ij[2]}'] = ('tr', ij, tr, ij)

    s = z3.Solver(); slin = z3.Solver()
    for n, e in ground:
        s.assert_and_track(e, n); slin.assert_and_track(e, n)
    counter = itertools.count()

    # ---- UNSAT core for queue restriction ----
    sc = z3.Solver(); sc.set('timeout', 180000)
    for n, e in ground:
        sc.assert_and_track(e, n)
    for n, (_, _, e, _) in ors.items():
        sc.assert_and_track(e, n)
    res = sc.check()
    if res != z3.unsat:
        return ['SPEC_SAT']
    core = set(str(u) for u in sc.unsat_core())
    order = sorted(n for n in ors if n in core)

    def push_disj(dj, tag, front):
        s.assert_and_track(dj, tag)
        for j, ch in enumerate(linear_strip(dj)):
            slin.assert_and_track(ch, f'{tag}c{j}')
        for ei, oc in enumerate(or_children(dj)):
            front.append(('sub', 'sub', tag, oc, (tag, ei)))

    def dfs(queue, qi):
        nd = next(counter)
        if nd > budget_nodes:
            return ['OVER']
        if verbose and nd % 20000 == 0:
            print(f'    node {nd} qi={qi}', flush=True)
        if slin.check() == z3.unsat:
            return ['term', sorted(str(u) for u in slin.unsat_core())]
        if s.check() == z3.unsat and qi >= len(queue):
            return ['NEEDS_SPLIT']
        if qi >= len(queue):
            return ['FAIL']
        name, typ, r, orexp, meta = queue[qi]
        kids = []
        for dj in disjs(orexp):
            s.push(); slin.push()
            front = []
            push_disj(dj, f'N{nd}', front)
            q2 = queue[:qi + 1] + front + queue[qi + 1:]
            kids.append(dfs(q2, qi + 1))
            s.pop(); slin.pop()
            if kids[-1][0] not in ('term', 'node'):
                return kids[-1]
        return ['node', nd, (typ, r, name, meta), kids]

    def live_arms(orexp):
        live = []
        for di, dj in enumerate(disjs(orexp)):
            slin.push()
            for ch in linear_strip(dj):
                slin.add(ch)
            if slin.check() != z3.unsat:
                live.append(di)
            slin.pop()
        return live

    def dfs_mrv(queue):
        """Queue-order-free MRV DFS: always split the core-or with
        fewest live disjuncts.  Each node re-ranks remaining ors."""
        nd = next(counter)
        if nd > budget_nodes:
            return ['OVER']
        if verbose and nd % 2000 == 0:
            print(f'    node {nd} depth-queued={len(queue)}', flush=True)
        if slin.check() == z3.unsat:
            return ['term', sorted(str(u) for u in slin.unsat_core())]
        if not queue:
            if s.check() == z3.unsat:
                return ['NEEDS_SPLIT']
            return ['FAIL']
        # choose or: existential/pattern ors first (they fix big-gap
        # positions and collapse the rest), then fewest live arms
        def sub_kind(orexp):
            """kind of a lazy sub-or inside a pushed disjunct."""
            djs = disjs(orexp)
            if all(str(c.decl().name()) == '=' for c in djs):
                return 'mem'                 # y = c_1 | ... | y = c_n
            if all(z3.is_and(c) for c in djs):
                return 'band'                # atomic band arms
            return 'nb'                      # z<=x | y<=z

        def prio(i):
            name, typ, r, orexp, meta = queue[i]
            if typ == 'sub':
                return {'band': 6, 'nb': 7, 'mem': 8}[sub_kind(orexp)]
            if typ != 'or':
                return 5
            tg = meta[2]
            return {'pat': 0, 'ex': 1, 'b3': 2, 'b2': 3, 'g': 4,
                    'spd': 9}.get(tg, 5)
        best_i, best_live = None, None
        for i in range(len(queue)):
            lv = live_arms(queue[i][3])
            key = (prio(i), len(lv))
            if best_live is None or key < best_live:
                best_i, best_live = i, key
                if key == (0, 0):
                    break
        name, typ, r, orexp, meta = queue[best_i]
        rest = queue[:best_i] + queue[best_i + 1:]
        kids = []
        for di, dj in enumerate(disjs(orexp)):
            s.push(); slin.push()
            front = []
            push_disj(dj, f'N{nd}', front)
            kids.append(dfs_mrv(front + rest))
            s.pop(); slin.pop()
            if kids[-1][0] not in ('term', 'node'):
                return kids[-1]
        return ['node', nd, (typ, r, name, meta), kids]

    queue = [(n, ors[n][0], ors[n][1], ors[n][2], ors[n][3])
             for n in order]
    return dfs_mrv(queue)


def count_nodes(tr):
    if tr[0] in ('term', 'FAIL', 'OVER', 'NEEDS_SPLIT', 'SPEC_SAT'):
        return 1
    return 1 + sum(count_nodes(k) for k in tr[3])


if __name__ == '__main__':
    for a in (0, 5):
        t0 = time.time()
        tr = build_tree(10, [(a, 's2')])
        print(f'P10 s2@{a}: {tr[0]} nodes={count_nodes(tr)} '
              f'({time.time()-t0:.1f}s)', flush=True)
