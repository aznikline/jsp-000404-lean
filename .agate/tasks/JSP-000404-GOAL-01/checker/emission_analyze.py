"""Emission analysis: for each LP-feasible cell assignment, enumerate
maximal feasible carry patterns and compute max weighted emission
sum_i 2^{k_i} E_i, where

    E_i = sum over adjacent gap pairs (a,b) at i of (2^{g(a,b)} - 1)
    g(a,b) = auto + carry,  auto = [m_a>=1 and m_b>=1]
    carry in {0,1} requires r_a+r_b >= 1 and is only useful if
    m_a+m_b >= 1.

A carry set S is feasible iff LP (base rows + r_a+r_b>=1 for (a,b) in S)
is feasible.  We enumerate MAXIMAL feasible sets via DFS pruning.
"""
import itertools
from fractions import Fraction as Fr
from del_lp import base_rows, lp_solve


def adj_pairs(s):
    """adjacent gap-index pairs in a fan of s-1 cyclic gaps."""
    return [(g, (g + 1) % (s - 1)) for g in range(s - 1)]


def pair_data(assign, s):
    """All (vertex, ga, gb) adjacent pairs with >=1 active cell."""
    out = []
    for v in range(s):
        for (a, b) in adj_pairs(s):
            if assign[v][a] >= 1 or assign[v][b] >= 1:
                out.append((v, v * (s - 1) + a, v * (s - 1) + b, a, b))
    return out


def max_emission(assign, n, s, delta):
    """Enumerate maximal feasible carry sets; return (best_weighted_E,
    best_set, ks).  E_i computed as sum over i's adjacent pairs of
    (2^{g}-1) with g = auto + carry."""
    nv = s * (s - 1)
    rows0 = base_rows(assign, n, s, delta)
    ks = [sum(max(m - 1, 0) for m in assign[v]) for v in range(s)]
    pairs = pair_data(assign, s)
    autos = {}   # (v) -> set of pair positions with both active
    for v in range(s):
        for (a, b) in adj_pairs(s):
            if assign[v][a] >= 1 and assign[v][b] >= 1:
                autos.setdefault(v, set()).add((a, b))

    def feasible(S):
        rows = list(rows0)
        for (_, x, y, _, _) in S:
            rows.append(({x: Fr(-1), y: Fr(-1)}, Fr(-1)))
        return lp_solve(rows, nv)

    def weighted_E(S):
        Sset = set(S)
        tot = 0
        for v in range(s):
            E = 0
            for (a, b) in adj_pairs(s):
                auto = 1 if (a, b) in autos.get(v, ()) else 0
                car = 0
                if (v, v * (s - 1) + a, v * (s - 1) + b, a, b) in Sset:
                    car = 1
                E += (2 ** (auto + car) - 1)
            tot += (2 ** ks[v]) * E
        return tot

    # greedy: add pairs in descending marginal value order
    def marg(p):
        v, _, _, a, b = p
        auto = 1 if (a, b) in autos.get(v, ()) else 0
        return (2 ** ks[v]) * (2 ** (auto + 1) - 2 ** auto)
    order = sorted(pairs, key=marg, reverse=True)
    if feasible(order):
        best = (weighted_E(order), list(order))
        return best[0], best[1], ks, pairs
    S = []
    for p in order:
        S.append(p)
        if not feasible(S):
            S.pop()
    best = (weighted_E(S), list(S))
    return best[0], best[1], ks, pairs


def analyze(assign, n, s, delta):
    """Return dict with F, max weighted emission, deficit, zero-emitter
    info under the best carry set."""
    wE, S, ks, pairs = max_emission(assign, n, s, delta)
    F = sum(2 ** k for k in ks)
    Sset = set(S)
    zeros = []
    Es = {}
    for v in range(s):
        E = 0
        for (a, b) in adj_pairs(s):
            auto = 1 if (assign[v][a] >= 1 and assign[v][b] >= 1) else 0
            car = 1 if (v, v * (s - 1) + a, v * (s - 1) + b, a, b) in Sset else 0
            E += (2 ** (auto + car) - 1)
        Es[v] = E
        if E == 0:
            zeros.append(v)
    return dict(F=F, wE=wE, deficit=wE - F, ks=ks, zeros=zeros, Es=Es,
                carries=S, pairs=pairs, assign=assign)


if __name__ == '__main__':
    import sys
    from del_lp2 import all_int_assignments
    n, d, s = 3, Fr(1, 4), 4
    Fmin = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    nv = s * (s - 1)
    aa = all_int_assignments(s, n, d)
    neg = tested = 0
    mindef = 10 ** 9
    marginals = []
    for a in aa:
        F = sum(2 ** sum(max(m - 1, 0) for m in v) for v in a)
        if F < Fmin:
            continue
        import weighted_lp as W
        if not W.int_constraints_ok(a, n, d, s):
            continue
        rows = base_rows(a, n, s, d)
        if not lp_solve(rows, nv):
            continue
        tested += 1
        r = analyze(a, n, s, d)
        if r['deficit'] < mindef:
            mindef = r['deficit']
            marginals = [r]
        elif r['deficit'] == mindef:
            marginals.append(r)
        if r['deficit'] < 0:
            neg += 1
            print('DEFICIT %d F=%d wE=%d ks=%s zeros=%s Es=%s' %
                  (r['deficit'], r['F'], r['wE'], r['ks'], r['zeros'],
                   r['Es']))
            print('   assign=%s' % (a,))
    print('tested feasible F>=%d: %d, deficit<0: %d, min deficit: %d (%d cases)'
          % (Fmin, tested, neg, mindef, len(marginals)))
    for r in marginals[:8]:
        print('  marginal: F=%d wE=%d ks=%s zeros=%s Es=%s' %
              (r['F'], r['wE'], r['ks'], r['zeros'], r['Es']))
        print('    assign=%s' % (r['assign'],))
