#!/usr/bin/env python3
"""Extract explicit decision trees for n=4 multiset leaf closures.

For every certificate leaf in tools/n4_cores.json, builds the scalar model
(tools/n4_model.py), restricts the disjunctive facts to the leaf's unsat core,
orders them by tools/n4_orders.json, then DFS-explores the case tree: at each
node it checks UNSAT of ground + chosen disjuncts; terminals record their
unsat core (tracked names) for `linarith only [...]` replay.

nb (adjacency) and sep components are stripped from the Z3 disjuncts and
re-introduced as queue ors after their parent disjunct is chosen — mirroring
exactly what the Lean proof must do (instantiate the ∀-component on a chord
and case-split it).

Output: tools/n4_leaf_trees.json   {cert: {key: tree}}
tree := ['term', [names]] | ['node', nd, emitinfo, [child, ...]]
emitinfo describes how to emit the split in Lean.
"""
import z3, itertools, json, sys, time, os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from n4_model import build, sig2_case, sig1_case, em_case, MEDPAIR, P

delta, t, d, Dm, p, base, trips = build()

CERTS = {
    'pair_A':    ([(1, 's2'), (3, 's1')], False),
    'pair_B':    ([(1, 's1'), (3, 's2')], False),
    'triple_A':  ([(1, 's2'), (2, 's1'), (4, 's1')], False),
    'triple_B':  ([(0, 's1'), (2, 's1'), (3, 's2')], False),
    'pair04_em': ([(0, 's2'), (4, 's2')], True),
}
PAIR12 = [(a, b) for a in range(4) for b in range(4) if a != b]
PERM3 = list(itertools.permutations(range(4), 3))
DJ = []
for _a in range(4):
    for _b in range(4):
        if _a == _b: continue
        _rest = [q for q in range(4) if q not in (_a, _b)]
        for (_u, _v) in itertools.permutations(_rest, 2):
            DJ.append((_a, _b, _u, _v))

def case_of(kind, c):
    if kind == 's1': return ('med', c)
    if c < 5: return ('hi', c)
    return ('medpair', MEDPAIR[c - 5])

def leaf_env(cert, key):
    """ground: [(leanname, expr)]; ors: name -> (typeinfo, orexpr)."""
    spec, hasem = CERTS[cert]
    ground = [('hplo', delta >= 0), ('hphi', delta < 1),
              ('ht0b', t[0] >= 0), ('ht4b', t[4] <= delta)]
    for i in range(4):
        ground.append((f'ht{i}{i+1}', t[i] < t[i + 1]))
    for i in range(5):
        for j in range(i + 1, 5):
            ground.append((f'hc{i}{j}',
                           z3.And(t[i] + 1 <= Dm(i, j), Dm(i, j) <= p - 1 + t[j])))
    ors = {}
    for (r, kind), c in zip(spec, key):
        S = [Dm(r, j) for j in range(5) if j != r]
        kind2, kk = case_of(kind, c)
        tv = t[r]
        def elo(v):
            for ci, x in enumerate(S): ground.append((f'u{r}e{ci}', x - tv >= v))
        def ehi(v):
            for ci, x in enumerate(S): ground.append((f'u{r}h{ci}', tv + p - x >= v))
        def span(B):
            for ci, x in enumerate(S):
                for cj, y in enumerate(S):
                    if ci != cj: ground.append((f'u{r}s{ci}{cj}', y - x < B))
        def emin(v): ors[f'E{r}_emin'] = ('emin', r, z3.Or(*[x - tv < v for x in S]))
        def emax(v): ors[f'E{r}_emax'] = ('emax', r, z3.Or(*[tv + p - x < v for x in S]))
        def cpair(lo, hi):
            ors[f'E{r}_bigk'] = ('bigk', r, z3.Or(*[
                z3.And(S[a] < S[b], S[b] - S[a] >= lo, S[b] - S[a] < hi)
                for (a, b) in PAIR12]))
        if kind2 == 'hi':
            if kk == 0: elo(3); span(6); emin(4); emax(2)
            elif kk == 4: ehi(3); span(6); emax(4); emin(2)
            else: cpair(3, 4); span(8); emin(2); emax(2)
        elif kind2 == 'med':
            if kk == 0: elo(2); span(6); emin(3); emax(2)
            elif kk == 4: ehi(2); span(6); emax(3); emin(2)
            else: cpair(2, 3); span(7); emin(2); emax(2)
        else:
            a, b = kk
            intern = [q for q in (a, b) if q in (1, 2, 3)]
            if 0 in (a, b): elo(2); emin(3)
            else: emin(2)
            if 4 in (a, b): ehi(2); emax(3)
            else: emax(2)
            m = len(intern)
            if m == 1: cpair(2, 3)
            elif m == 2:
                ors[f'E{r}_big2'] = ('big2', r, z3.Or(*(
                    [z3.And(S[a] < S[b], S[b] < S[c],
                            S[b] - S[a] >= 2, S[b] - S[a] < 3,
                            S[c] - S[b] >= 2, S[c] - S[b] < 3)
                     for (a, b, c) in PERM3] +
                    [z3.And(S[a] < S[b], S[b] - S[a] >= 2, S[b] - S[a] < 3,
                            S[u] < S[v], S[v] - S[u] >= 2, S[v] - S[u] < 3)
                     for (a, b, u, v) in DJ])))
                ors[f'E{r}_sml'] = ('sml', r, z3.Or(*[
                    z3.And(S[a] <= S[b], S[b] - S[a] < 2) for (a, b) in PAIR12]))
            span(m + 6)
    if hasem:
        ors['em'] = ('em', -1, z3.Or(*[
            em_case(t, Dm, p, r, w)
            for r, w in [(0, 1), (0, 2), (0, 3), (4, 1), (4, 2), (4, 3)]]))
    for ij, tr in trips.items():
        ors[f'tr{ij[0]}{ij[1]}{ij[2]}'] = ('tr', ij, tr)
    return ground, ors

def pair_atoms(expr):
    """(x, y) from the first conjunct `x < y` or `x <= y` of a disjunct."""
    a = expr.children()[0] if z3.is_and(expr) else expr
    return a.children()[0], a.children()[1]

def extras_for(name, typ, r, di, S, zsets):
    """queue ors to insert after choosing disjunct di of or `name`.
    Returns (front, back): refined z-sets go right after this node, fallback
    chords go to the end of the queue — the DFS only reaches them if every
    other split failed to close the branch."""
    front, back = [], []
    ref = zsets.get(f'{r}_{typ}', [])
    fzs = list(ref)
    bzs = [z for z in range(4) if z not in ref]
    if typ in ('bigk', 'sml'):
        # parent comp index: bigk nb at 3, sml nb at 2
        ci = 3 if typ == 'bigk' else 2
        front += [('NBWAIT', name, di, ci, z) for z in fzs]
        back += [('NBWAIT', name, di, ci, z) for z in bzs]
        return front, back
    if typ == 'big2':
        comps = [4, 7] if di < 24 else [3, 7]
        for comp in comps:
            front += [('NBWAIT', name, di, comp, z) for z in fzs]
            back += [('NBWAIT', name, di, comp, z) for z in bzs]
        if di >= 24:
            front.append(('SEPWAIT', name, di, 8))
    return front, back

def build_tree(cert, keystr, key, orders, cores, nbsets):
    spec, hasem = CERTS[cert]
    ground, ors = leaf_env(cert, key)
    core = cores[cert][keystr]
    order = [n for n in orders[cert][keystr]['order'] if n in core]
    zsets = nbsets.get(cert, {}).get(keystr, {})
    Srows = {r: [Dm(r, j) for j in range(5) if j != r] for (r, _) in spec}
    s = z3.Solver()
    for n, e in ground:
        s.assert_and_track(e, n)
    counter = itertools.count()

    def disjs(e):
        return e.children() if z3.is_or(e) else [e]

    def dfs(queue, qi):
        nd = next(counter)
        if s.check() == z3.unsat:
            return ['term', sorted(str(u) for u in s.unsat_core())]
        if qi >= len(queue):
            return ['FAIL']
        name, typ, r, orexp, emitmeta = queue[qi]
        kids = []
        for di, dj in enumerate(disjs(orexp)):
            s.push()
            s.assert_and_track(dj, f'N{nd}')
            # extra queue ors unlocked by this disjunct
            front, back = [], []
            fr, bk = extras_for(name, typ, r, di, Srows.get(r, []), zsets)
            for w in fr:
                if w[0] == 'NBWAIT':
                    _, pname, pdi, comp, z = w
                    x, y = pair_atoms(dj) if typ != 'big2' else big2_pair(dj, pdi, comp)
                    front.append(('nbz', 'nbz', r,
                                  z3.Or(Srows[r][z] <= x, y <= Srows[r][z]),
                                  (nd, comp, z)))
                elif w[0] == 'SEPWAIT':
                    _, pname, pdi, comp = w
                    x, y, u, v = big2_pair4(dj)
                    front.append(('sep', 'sep', r,
                                  z3.Or(y <= u, v <= x), (nd, comp)))
            for w in bk:
                _, pname, pdi, comp, z = w
                x, y = pair_atoms(dj) if typ != 'big2' else big2_pair(dj, pdi, comp)
                back.append(('nbz', 'nbz', r,
                             z3.Or(Srows[r][z] <= x, y <= Srows[r][z]),
                             (nd, comp, z)))
            q2 = queue[:qi + 1] + front + queue[qi + 1:] + back
            kids.append(dfs(q2, qi + 1))
            s.pop()
            if kids and kids[-1][0] == 'FAIL':
                return ['FAIL']
        return ['node', nd, (typ, r, name, emitmeta), kids]

    queue = [(n, ors[n][0], ors[n][1], ors[n][2], None) for n in order]
    return dfs(queue, 0)

def big2_pair(dj, pdi, comp):
    """(x, y) guarded by nb component `comp` of big2 disjunct pdi."""
    ch = dj.children()
    if pdi < 24:  # chain: x<y ∧ y<z ∧ gaps...
        x = ch[0].children()[0]; y = ch[0].children()[1]; z = ch[1].children()[1]
        return (x, y) if comp == 4 else (y, z)
    x = ch[0].children()[0]; y = ch[0].children()[1]
    u = ch[3].children()[0]; v = ch[3].children()[1]
    return (x, y) if comp == 3 else (u, v)

def big2_pair4(dj):
    ch = dj.children()
    x = ch[0].children()[0]; y = ch[0].children()[1]
    u = ch[3].children()[0]; v = ch[3].children()[1]
    return x, y, u, v

def main():
    cores = json.load(open(os.path.join(HERE, 'n4_cores.json')))
    orders = json.load(open(os.path.join(HERE, 'n4_orders.json')))
    nbsets = json.load(open(os.path.join(HERE, 'n4_nb_sets.json')))
    only = sys.argv[1] if len(sys.argv) > 1 else None
    out = {}
    t0 = time.time()
    for cert, m in cores.items():
        for kstr, c in m.items():
            if c == 'SAT': continue
            if only and not (cert == only.split(':')[0] and kstr == only.split(':')[1]):
                continue
            key = tuple(int(v) for v in kstr.split(','))
            tree = build_tree(cert, kstr, key, orders, cores, nbsets)
            out.setdefault(cert, {})[kstr] = tree
            n = count_nodes(tree)
            print(cert, kstr, 'nodes', n, flush=True)
    fn = os.path.join(HERE, 'n4_leaf_trees.json' if not only else
                      f'/tmp/tree_{only.replace(":", "_")}.json')
    json.dump(out, open(fn, 'w'))
    print('done', round(time.time() - t0, 1), '->', fn)

def count_nodes(tr):
    if tr[0] in ('term', 'FAIL'): return 1
    return 1 + sum(count_nodes(k) for k in tr[3])

if __name__ == '__main__':
    main()
