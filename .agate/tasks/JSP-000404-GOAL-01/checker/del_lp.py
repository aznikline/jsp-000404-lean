"""Deletion induction step test: for LP-feasible cell assignments, does
there always exist a feasible remainder r and vertex t with

    2^{k_t} <= sum_i 2^{k_i} (2^{g_it(r)} - 1)   ?

gain_it(r) = auto_it + carry_it(r), where
  auto_it  = 1 iff both flanks of dir(i->t) active (m_a,m_b >= 1)
  carry_it = 1 iff r_a+r_b >= 1 AND at least one flank active

We may CHOOSE r.  For each t, the cert is monotone in carries, so test:
add all carry constraints r_a+r_b>=1 at active-flank pairs toward t; if
LP stays feasible, max gains achieved -> evaluate cert.
"""
import itertools
from fractions import Fraction as Fr
from weighted_lp import blocks_of


def lp_solve(rows, nv):
    """Exact phase-I feasibility.  rows: list of (dict coeffs, b) meaning
    sum coeff*x <= b.  Returns True/False."""
    m = len(rows)
    nr = nv + 2 * m
    T = [[Fr(0)] * (nr + 1) for _ in range(m + 1)]
    art = nv + m
    obj = [Fr(0)] * (nr + 1)
    for i, (co, b) in enumerate(rows):
        sgn = 1
        if b < 0:
            co = {k: -x for k, x in co.items()}
            b = -b
            sgn = -1
        for k, x in co.items():
            T[i][k] = x
        T[i][nv + i] = Fr(sgn)
        obj[nv + i] += Fr(sgn)
        T[i][art + i] = Fr(1)
        T[i][nr] = b
        for k, x in co.items():
            obj[k] += x
        obj[nr] += b
    for c in range(nr + 1):
        T[m][c] = obj[c]
    basis = [art + i for i in range(m)]
    it = 0
    while it < 60000:
        it += 1
        c = next((c for c in range(nr) if T[m][c] > 0), None)
        if c is None:
            break
        br = -1
        bv = None
        for i in range(m):
            if T[i][c] > 0:
                r = T[i][nr] / T[i][c]
                if bv is None or r < bv or (r == bv and basis[i] > basis[br]):
                    bv = r
                    br = i
        if br < 0:
            return True  # unbounded phase-I optimum can't happen; treat feas
        p = T[br][c]
        T[br] = [x / p for x in T[br]]
        for i in range(m + 1):
            if i != br and T[i][c] != 0:
                k = T[i][c]
                T[i] = [x - k * y for x, y in zip(T[i], T[br])]
        basis[br] = c
    return T[m][nr] == 0


def base_rows(assign, n, s, delta):
    """VERT + TRI equality rows + r>=0 + r<=1 (strict weakened to <=)."""
    nv = s * (s - 1)
    rows = []
    for v in range(s):
        b = Fr(n) + delta - sum(assign[v])
        co = {v * (s - 1) + g: Fr(1) for g in range(s - 1)}
        rows.append((dict(co), b))
        rows.append(({k: -x for k, x in co.items()}, -b))
    for (a, b, c) in itertools.combinations(range(s), 3):
        co = {}
        C = 0
        for (v, j, k) in ((a, b, c), (b, a, c), (c, a, b)):
            for g in blocks_of(v, j, k, s):
                co[v * (s - 1) + g] = co.get(v * (s - 1) + g, Fr(0)) + 1
                C += assign[v][g]
        bb = Fr(n) + delta - C
        rows.append((dict(co), bb))
        rows.append(({k: -x for k, x in co.items()}, -bb))
    for i in range(nv):
        rows.append(({i: Fr(-1)}, Fr(0)))
        rows.append(({i: Fr(1)}, Fr(1)))  # r <= 1 (boundary allowed, harmless)
    return rows


def cert_exists(assign, n, s, delta):
    """For each t, try to find feasible r making cert hold.
    Carries chosen greedily: test the all-carry extension first."""
    nv = s * (s - 1)
    rows0 = base_rows(assign, n, s, delta)
    ks = [sum(max(m - 1, 0) for m in assign[v]) for v in range(s)]
    best = []
    for t in range(s):
        # flank pairs toward t: at each i != t, the two gaps adjacent to
        # dir(i->t).  In our gap indexing, dir(i->t) sits between gaps
        # pos(t)-1 and pos(t) in i's fan order (cyclic).
        # pos of t in i's fan = t if t < i else t - 1
        carry_pairs = []
        for i in range(s):
            if i == t:
                continue
            pos = t if t < i else t - 1
            ga = (pos - 1) % (s - 1)
            gb = pos % (s - 1)
            ma, mb = assign[i][ga], assign[i][gb]
            if ma >= 1 or mb >= 1:  # carry can only help if a flank active
                carry_pairs.append((i * (s - 1) + ga, i * (s - 1) + gb))
        # try all-carries first (monotone: max gains)
        def feasible_with(pairs):
            rows = list(rows0)
            for (x, y) in pairs:
                rows.append(({x: Fr(-1), y: Fr(-1)}, Fr(-1)))  # -(r_a+r_b) <= -1
            return lp_solve(rows, nv)
        if feasible_with(carry_pairs):
            gains = []
            for i in range(s):
                if i == t:
                    gains.append(0)
                    continue
                pos = t if t < i else t - 1
                ga = (pos - 1) % (s - 1)
                gb = pos % (s - 1)
                ma, mb = assign[i][ga], assign[i][gb]
                auto = 1 if (ma >= 1 and mb >= 1) else 0
                car = 1 if (ma >= 1 or mb >= 1) else 0
                gains.append(auto + car)
            inc = sum((2 ** ks[i]) * (2 ** gains[i] - 1)
                      for i in range(s) if i != t)
            best.append((t, inc, 2 ** ks[t], inc >= 2 ** ks[t], 'all'))
            continue
        # subset search over carry pairs (bounded)
        found = None
        for sz in range(len(carry_pairs), -1, -1):
            for sub in itertools.combinations(carry_pairs, sz):
                if feasible_with(list(sub)):
                    sub = set(sub)
                    gains = []
                    for i in range(s):
                        if i == t:
                            gains.append(0)
                            continue
                        pos = t if t < i else t - 1
                        ga = (pos - 1) % (s - 1)
                        gb = pos % (s - 1)
                        ma, mb = assign[i][ga], assign[i][gb]
                        auto = 1 if (ma >= 1 and mb >= 1) else 0
                        pr = (i * (s - 1) + ga, i * (s - 1) + gb)
                        car = 1 if pr in sub else 0
                        gains.append(auto + car)
                    inc = sum((2 ** ks[i]) * (2 ** gains[i] - 1)
                              for i in range(s) if i != t)
                    if inc >= 2 ** ks[t]:
                        found = (t, inc, 2 ** ks[t], True, f'sub{sz}')
                        break
            if found:
                break
        best.append(found or (t, None, 2 ** ks[t], False, 'none'))
    return ks, best


if __name__ == '__main__':
    # test on the known LP-feasible assignments
    tests = [
        # s=4 cap-achieving staircase-ish and the delta-high F=20
        ([(0, 0, 3), (0, 0, 4), (0, 3, 1), (3, 0, 1)], 4, 4, Fr(3, 4)),
        ([(0, 0, 4), (0, 0, 4), (0, 3, 1), (3, 0, 1)], 4, 4, Fr(3, 4)),
        # s=5 F=17 violator-pattern (though LP-infeasible; sanity)
    ]
    for (a, n, s, d) in tests:
        ks, best = cert_exists(a, n, s, d)
        print('assign=%s ks=%s' % (a, ks))
        for row in best:
            print('   t=%s inc=%s need=%s ok=%s mode=%s' % row)
