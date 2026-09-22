"""Fast cert-existence test: for LP-feasible assignments, is there a
vertex t and feasible carry set with

    inc(t) = sum_i 2^{k_i}(2^{g_it}-1) >= 2^{k_t} ?

g_it = auto_it + carry_it;  carry_it needs r_a+r_b>=1 at i's flank pair.
Two-phase: (1) auto gains only -- free; (2) greedy carries by marginal
value, one LP check; (3) fall back to subset enumeration (rare).
"""
import itertools
from fractions import Fraction as Fr
from weighted_lp import blocks_of, per_vertex_options, int_constraints_ok
from del_lp import base_rows, lp_solve


def flank_pair(i, t, s):
    """gap indices (in i's fan, size s-1) flanking dir(i->t).
    Cyclic fan convention (matching blocks_of): direction to j sits at
    position (j-i) mod s - 1."""
    pos = (t - i) % s - 1
    return ((pos - 1) % (s - 1), pos % (s - 1))


def cert_exists_fast(assign, n, s, delta, verbose=False):
    nv = s * (s - 1)
    rows0 = base_rows(assign, n, s, delta)
    ks = [sum(max(m - 1, 0) for m in assign[v]) for v in range(s)]
    results = []
    for t in range(s):
        need = 2 ** ks[t]
        pairs = []          # (i, ga, gb, active) carry candidates
        auto_contrib = {}   # i -> auto gain
        for i in range(s):
            if i == t:
                continue
            ga, gb = flank_pair(i, t, s)
            ma, mb = assign[i][ga], assign[i][gb]
            auto_contrib[i] = 1 if (ma >= 1 and mb >= 1) else 0
            if ma >= 1 or mb >= 1:
                pairs.append((i, i * (s - 1) + ga, i * (s - 1) + gb))
        inc_auto = sum((2 ** ks[i]) * (2 ** auto_contrib[i] - 1)
                       for i in auto_contrib)
        if inc_auto >= need:
            results.append((t, inc_auto, need, True, 'auto'))
            continue
        # greedy: carries add 2^{k_i} * 2^{auto_i} each
        cand = sorted(pairs, key=lambda p: -(2 ** ks[p[0]]) * (2 ** auto_contrib[p[0]]))
        chosen = []
        inc = inc_auto
        for p in cand:
            if inc >= need:
                break
            chosen.append(p)
            inc += (2 ** ks[p[0]]) * (2 ** auto_contrib[p[0]])
        def feas(ps):
            rows = list(rows0)
            for (_, x, y) in ps:
                rows.append(({x: Fr(-1), y: Fr(-1)}, Fr(-1)))
            return lp_solve(rows, nv)
        if inc >= need and feas(chosen):
            results.append((t, inc, need, True, f'greedy{len(chosen)}'))
            continue
        # fallback: enumerate subsets of candidate pairs
        got = False
        for sz in range(len(cand), -1, -1):
            for sub in itertools.combinations(cand, sz):
                if not feas(list(sub)):
                    continue
                ss = set(sub)
                inc2 = inc_auto
                for p in cand:
                    if p in ss:
                        inc2 += (2 ** ks[p[0]]) * (2 ** auto_contrib[p[0]])
                if inc2 >= need:
                    results.append((t, inc2, need, True, f'sub{sz}'))
                    got = True
                    break
            if got:
                break
        if not got:
            results.append((t, None, need, False, 'none'))
    return ks, results


def all_int_assignments(s, n, delta):
    opts = per_vertex_options(s, n)
    out = []
    assign = [None] * s
    def dfs(v):
        if v == s:
            out.append([tuple(a) for a in assign])
            return
        for (cells, k) in opts:
            assign[v] = cells
            if int_constraints_ok(assign, n, delta, s, upto=v):
                dfs(v + 1)
        assign[v] = None
    dfs(0)
    return out


if __name__ == '__main__':
    import sys
    for (n, d) in [(3, Fr(1, 4)), (3, Fr(3, 4)), (4, Fr(1, 4)), (4, Fr(3, 4))]:
        s = 4
        nv = s * (s - 1)
        aa = all_int_assignments(s, n, d)
        feas = [a for a in aa if lp_solve(base_rows(a, n, s, d), nv)]
        print('n=%d d=%s: int=%d LP-feasible=%d' % (n, d, len(aa), len(feas)))
        bad = 0
        for a in feas:
            ks, res = cert_exists_fast(a, n, s, d)
            if not any(r[3] for r in res):
                bad += 1
                print('   NO-CERT %s ks=%s' % (a, ks))
        print('   feasible without cert: %d' % bad, flush=True)
