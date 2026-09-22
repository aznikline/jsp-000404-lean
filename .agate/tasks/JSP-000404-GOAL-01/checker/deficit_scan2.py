"""DFS-collect all debt-ok assignments with F >= Fmin, then LP + emission
check.  Reports max deficit F - wE."""
import sys
from fractions import Fraction as Fr
from del_lp import base_rows, lp_solve
from emission_analyze import max_emission
import weighted_lp as W


def collect(n, s, d, Fmin):
    opts = sorted(W.per_vertex_options(s, n), key=lambda x: -x[1])
    assign = [None] * s
    out = []
    Fpart = [0]

    def dfs(v, kmax):
        if not W.int_constraints_ok(assign, n, d, s, upto=v):
            return
        if Fpart[0] + (s - v) * (1 << kmax) < Fmin:
            return
        if v == s:
            if W.int_constraints_ok(assign, n, d, s) and Fpart[0] >= Fmin:
                ok, _ = W.debt_ok(assign, n, d, s)
                if ok:
                    out.append([tuple(a) for a in assign])
            return
        for (cells, k) in opts:
            if v > 0 and k > kmax:
                break
            assign[v] = cells
            Fpart[0] += 1 << k
            dfs(v + 1, k if v == 0 else kmax)
            Fpart[0] -= 1 << k
        assign[v] = None
    dfs(0, n - 1)
    return out


def scan(n, s, d, Fmin):
    nv = s * (s - 1)
    cand = collect(n, s, d, Fmin)
    tested = 0
    worst = -10 ** 9
    worst_a = None
    for a in cand:
        if not lp_solve(base_rows(a, n, s, d), nv):
            continue
        tested += 1
        wE, S, ks, _ = max_emission(a, n, s, d)
        deficit = sum(2 ** k for k in ks) - wE
        if deficit > worst:
            worst, worst_a = deficit, (a, ks, wE)
    print('n=%d s=%d d=%s Fmin=%d: cand=%d feasible=%d max-deficit=%d slack=%d %s'
          % (n, s, d, Fmin, len(cand), tested, worst, s - 1, worst_a),
          flush=True)


for args in [(4, 4, Fr(1, 4), 14), (4, 4, Fr(3, 4), 14),
             (5, 4, Fr(1, 4), 28), (4, 5, Fr(1, 4), 13),
             (4, 5, Fr(3, 4), 16)]:
    scan(*args)
