"""Extract decision trees for the 540 canonical S7/S8 combos.

Port of n4_extract_trees.py, parameterised by P and driven by the
canonical signature classes (no link, no M_II — it is corridor-excluded
upstream).

Tree: ['term', [names]] | ['node', nd, emitinfo, [kids]] | ['FAIL']
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


def pair_atoms(expr):
    a = expr.children()[0] if z3.is_and(expr) else expr
    return a.children()[0], a.children()[1]


def leaf_core(P, spec, combo, timeout=60000):
    ground, ors = leaf_env(P, spec, combo)
    s = z3.Solver(); s.set("timeout", timeout)
    for n, e in ground:
        s.assert_and_track(e, n)
    for n, (_, _, e) in ors.items():
        s.assert_and_track(e, n)
    if s.check() != z3.unsat:
        return 'SAT'
    return sorted(str(u) for u in s.unsat_core())


def disjs(e):
    return e.children() if z3.is_or(e) else [e]


def tree_size(s, orl, budget):
    cnt = [0]
    def dfs(i):
        cnt[0] += 1
        if cnt[0] > budget:
            return 'OVER'
        if s.check() == z3.unsat:
            return None
        if i == len(orl):
            return 'FAIL'
        for dj in disjs(orl[i]):
            s.push(); s.add(dj); r = dfs(i + 1); s.pop()
            if r:
                return r
        return None
    r = dfs(0)
    return cnt[0], r


def best_order(P, spec, combo, core, budget=200000):
    """Measure REAL tree size under each ordering by building it."""
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
        best = (count_nodes(build_tree(P, spec, combo,
                                       cands['T'],
                                       budget_nodes=4_000_000)),
                'T', cands['T'])
    return best


def build_tree(P, spec, combo, order, budget_nodes=2_000_000):
    ground, ors = leaf_env(P, spec, combo)
    Srows = {r: [D_ for D_ in []] for (r, _) in spec}   # filled below
    delta, t, d, D, p, base, trips = build(P)
    # NB: leaf_env uses its OWN d table; rebuild Srows from it
    Srows = {}
    for (r, _) in spec:
        pass
    # rebuild consistent vars: leaf_env creates fresh vars each call —
    # we must share one env. Re-do env inline.
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
    Srows = {}
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
    for n, e in ground:
        s.assert_and_track(e, n)
    counter = itertools.count()
    nchords = P - 1

    def extras_for(name, typ, r, di, dj):
        front, back = [], []
        if typ == 'bigk':
            x, y = pair_atoms(dj)
            for z_ in range(nchords):
                front.append(('nbz', 'nbz', r,
                              z3.Or(Srows[r][z_] <= x, y <= Srows[r][z_]),
                              (di, 3, z_)))
        return front, back

    def dfs(queue, qi):
        nd = next(counter)
        if nd > budget_nodes:
            return ['OVER']
        if s.check() == z3.unsat:
            return ['term', sorted(str(u) for u in s.unsat_core())]
        if qi >= len(queue):
            return ['FAIL']
        name, typ, r, orexp, emitmeta = queue[qi]
        kids = []
        for di, dj in enumerate(disjs(orexp)):
            s.push()
            s.assert_and_track(dj, f'N{nd}')
            fr, bk = extras_for(name, typ, r, di, dj)
            q2 = queue[:qi + 1] + fr + queue[qi + 1:] + bk
            kids.append(dfs(q2, qi + 1))
            s.pop()
            if kids and kids[-1][0] in ('FAIL', 'OVER'):
                return ['FAIL']
        return ['node', nd, (typ, r, name, emitmeta), kids]

    queue = [(n, ors[n][0], ors[n][1], ors[n][2], None) for n in order]
    return dfs(queue, 0)


def count_nodes(tr):
    if tr[0] in ('term', 'FAIL', 'OVER'):
        return 1
    return 1 + sum(count_nodes(k) for k in tr[3])


def count_terms(tr):
    if tr[0] == 'term':
        return 1
    if tr[0] in ('FAIL', 'OVER'):
        return 0
    return sum(count_terms(k) for k in tr[3])


def sample():
    """3 representative leaves per the Lead's instruction."""
    jobs = [
        ('s7_AA2', ('H_L', 'H_L', 'L_0')),          # endpoint class
        ('s7_AA2', ('H_I', 'H_I', 'L_I')),          # cpair/nb internal
        ('s8_BT', ('H_L', 'H_R')),                  # S8 between
    ]
    for cert, combo in jobs:
        P, spec = CERTS[cert]
        t0 = time.time()
        core = leaf_core(P, spec, combo)
        if core == 'SAT':
            print(cert, combo, 'SAT!?'); continue
        bo = best_order(P, spec, combo, core)
        print(cert, combo, 'core', len(core), 'order', bo[1],
              'est nodes', bo[0], f'({time.time()-t0:.0f}s)', flush=True)
        tree = build_tree(P, spec, combo, bo[2])
        print('   tree nodes', count_nodes(tree),
              'terms', count_terms(tree),
              'status', tree[0], f'({time.time()-t0:.0f}s)', flush=True)


if __name__ == '__main__':
    sample()
