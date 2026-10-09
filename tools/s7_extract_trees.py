"""Extract decision trees for the 540 canonical S7/S8 combos.

Port of n4_extract_trees.py, parameterised by P and driven by the
canonical signature classes (no link, no M_II — it is corridor-excluded
upstream).

Terminal purity: two solvers are maintained.
  s_full: pushes each chosen disjunct WHOLESALE (a bigk disjunct
          carries its nb = And-of-Ors inside) — mirrors the Z3 model.
  s_lin : pushes only the LINEAR components of each chosen disjunct
          plus chosen nbz branches — mirrors what `linarith only`
          can see in Lean.

A node closes only when s_lin is UNSAT ('term', linear core names).
If s_full is UNSAT but s_lin is not, the DFS keeps splitting the
queued disjunctions (pending nbz ors sit at the queue front).

Tree: ['term', [names]] | ['node', nd, emitinfo, [kids]] | ['FAIL']
      ['OVER'] | 'SAT' | 'UNKNOWN'
"""
import z3, itertools, json, sys, time, os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s7_canon import (build, nb, gap_sig_case, canon2, canon1,
                      sig2_of_class, sig1_of_class,
                      CANON2_ORDER, CANON1_ORDER)

# (name, P, spec rows [(row, kind)])
CERTS = {
    's7_AA2': (6, [(0, 's2'), (1, 's2'), (2, 's1')]),
    's7_AA5': (6, [(0, 's2'), (1, 's2'), (5, 's1')]),
    's7_AB0': (6, [(4, 's2'), (5, 's2'), (0, 's1')]),
    's7_AB3': (6, [(4, 's2'), (5, 's2'), (3, 's1')]),
    's8_AA':  (7, [(0, 's2'), (1, 's2')]),
    's8_BT':  (7, [(0, 's2'), (6, 's2')]),
    's8_AB':  (7, [(5, 's2'), (6, 's2')]),
}

CASES2 = [c for c in CANON2_ORDER if c != 'M_II']


def leaf_env(P, spec, combo):
    """ground: [(name, expr)]; ors: name -> (typ, row, orexpr)."""
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
    ors = {}
    for (r, kind), c in zip(spec, combo):
        S = [D(r, j) for j in range(P) if j != r]
        fn = sig2_of_class if kind == 's2' else sig1_of_class
        U, E = fn(P, t[r], S, p, c)
        for ci, (tag, e) in enumerate(U):
            ground.append((f'u{r}{tag}{ci}', e))
        for ei, (tag, e) in enumerate(E):
            ors[f'E{r}_{tag}{ei}'] = (tag, r, e)
    for ij, tr in trips.items():
        ors[f'tr{ij[0]}{ij[1]}{ij[2]}'] = ('tr', ij, tr)
    return ground, ors


def leaf_core(P, spec, combo, timeout=60000):
    """Returns (status, core|reason): status in UNSAT/SAT/UNKNOWN."""
    ground, ors = leaf_env(P, spec, combo)
    s = z3.Solver(); s.set("timeout", timeout)
    for n, e in ground:
        s.assert_and_track(e, n)
    for n, (_, _, e) in ors.items():
        s.assert_and_track(e, n)
    r = s.check()
    if r == z3.unsat:
        return 'UNSAT', sorted(str(u) for u in s.unsat_core())
    if r == z3.sat:
        return 'SAT', None
    return 'UNKNOWN', s.reason_unknown()


def disjs(e):
    return e.children() if z3.is_or(e) else [e]


def linear_strip(dj):
    """Linear-only shadow of a pushed disjunct.

    bigk/sml/big2 disjuncts embed nb(S,x,y) = And over z of Ors.
    Keep every child that is NOT such an And-of-Ors / Or.
    Returns a list of linear conjuncts.
    """
    out = []
    for ch in (dj.children() if z3.is_and(dj) else [dj]):
        # an nb conjunct is And of Ors, or a bare Or
        if z3.is_or(ch):
            continue
        if z3.is_and(ch) and any(z3.is_or(g) for g in ch.children()):
            continue
        out.append(ch)
    return out


def build_tree(P, spec, combo, order, budget_nodes=4_000_000):
    """Dual-solver DFS; terminal iff the LINEAR shadow is UNSAT."""
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
    ors, Srows = {}, {}
    for (r, kind), c in zip(spec, combo):
        S = [D(r, j) for j in range(P) if j != r]
        Srows[r] = S
        fn = sig2_of_class if kind == 's2' else sig1_of_class
        U, E = fn(P, t[r], S, p, c)
        for ci, (tag, e) in enumerate(U):
            ground.append((f'u{r}{tag}{ci}', e))
        for ei, (tag, e) in enumerate(E):
            ors[f'E{r}_{tag}{ei}'] = (tag, r, e)
    for ij, tr in trips.items():
        ors[f'tr{ij[0]}{ij[1]}{ij[2]}'] = ('tr', ij, tr)

    s = z3.Solver()
    slin = z3.Solver()
    for n, e in ground:
        s.assert_and_track(e, n)
        slin.assert_and_track(e, n)
    counter = itertools.count()
    nchords = P - 1

    def push_disj(name, typ, r, dj, tag):
        s.assert_and_track(dj, tag)
        for j, ch in enumerate(linear_strip(dj)):
            slin.assert_and_track(ch, f'{tag}c{j}')

    def dfs(queue, qi):
        nd = next(counter)
        if nd > budget_nodes:
            return ['OVER']
        if slin.check() == z3.unsat:
            return ['term', sorted(str(u) for u in slin.unsat_core())]
        if s.check() == z3.unsat and qi >= len(queue):
            return ['NEEDS_SPLIT']  # full-context UNSAT with no ors left
        if qi >= len(queue):
            return ['FAIL']
        name, typ, r, orexp, emitmeta = queue[qi]
        kids = []
        for di, dj in enumerate(disjs(orexp)):
            s.push(); slin.push()
            push_disj(name, typ, r, dj, f'N{nd}')
            front = []
            if typ in ('bigk', 'sml'):
                ci = 3 if typ == 'bigk' else 2
                x, y = pair_atoms(dj)
                for z_ in range(nchords):
                    front.append(('nbz', 'nbz', r,
                                  z3.Or(Srows[r][z_] <= x,
                                        y <= Srows[r][z_]),
                                  (nd, di, ci, z_)))
            q2 = queue[:qi + 1] + front + queue[qi + 1:]
            kids.append(dfs(q2, qi + 1))
            s.pop(); slin.pop()
            if kids and kids[-1][0] in ('FAIL', 'OVER', 'NEEDS_SPLIT'):
                return ['FAIL']
        return ['node', nd, (typ, r, name, emitmeta), kids]

    queue = [(n, ors[n][0], ors[n][1], ors[n][2], None) for n in order]
    return dfs(queue, 0)


def pair_atoms(expr):
    a = expr.children()[0] if z3.is_and(expr) else expr
    return a.children()[0], a.children()[1]


def best_order(P, spec, combo, core, budget=200000):
    ground, ors = leaf_env(P, spec, combo)
    ornames = [n for n in core if n in ors]
    cands = {
        'T': sorted(ornames, key=lambda n: (not n.startswith('tr'), n)),
        'E': sorted(ornames, key=lambda n: (n.startswith('tr'), n)),
    }
    best = None
    for mode, orl in cands.items():
        tr = build_tree(P, spec, combo, orl, budget_nodes=budget)
        n_ = count_nodes(tr)
        if tr[0] not in ('FAIL', 'OVER') and (best is None or n_ < best[0]):
            best = (n_, mode, orl)
    if best is None:
        best = (count_nodes(build_tree(P, spec, combo, cands['T'],
                                       budget_nodes=4_000_000)),
                'T', cands['T'])
    return best


def count_nodes(tr):
    if tr[0] in ('term', 'FAIL', 'OVER', 'NEEDS_SPLIT'):
        return 1
    return 1 + sum(count_nodes(k) for k in tr[3])


def count_terms(tr):
    if tr[0] == 'term':
        return 1
    if tr[0] in ('FAIL', 'OVER', 'NEEDS_SPLIT'):
        return 0
    return sum(count_terms(k) for k in tr[3])
