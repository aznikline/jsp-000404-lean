"""Soundness check for the s-generic model on REAL configurations.

For random s-point configs: compute per-vertex fan order, gaps,
side signs and exponent from actual Euclidean geometry; find the
matching variant in generic_model's VV (existence proves the
generalized side/lift rule is consistent); then evaluate every
ORIG constraint numerically.

Equalities and nonnegativity must hold exactly; ∠≤π−λ / facing
bounds may fail (config not assumed legal) — they are reported
separately.

Usage: validate_real_generic.py [s] [n] [trials]
"""
import sys, math, random
sys.path.insert(0, '.')
import generic_model as gm

def skel(P, n, lam):
    s = len(P)
    V = []
    for i in range(s):
        dirs = {j: math.atan2(P[j][1] - P[i][1],
                              P[j][0] - P[i][0]) % math.pi
                for j in range(s) if j != i}
        order = sorted(dirs, key=lambda j: dirs[j])
        angs = [dirs[j] for j in order]
        m = s - 1
        gaps = [((angs[(t + 1) % m] - angs[t]) % math.pi) / math.pi
                for t in range(m)]
        qs = tuple(int(math.floor(g / lam)) for g in gaps)
        side = {}
        for j in order:
            for k in order:
                if k == j:
                    continue
                cr = ((P[j][0] - P[i][0]) * (P[k][1] - P[i][1])
                      - (P[j][1] - P[i][1]) * (P[k][0] - P[i][0]))
                side[(j, k)] = 1 if cr > 0 else -1
        kv = sum(max(q - 1, 0) for q in qs)
        V.append(dict(order=order, gaps=gaps, qs=qs, side=side,
                      kv=kv))
    return V

def find_variant(VV_i, sk):
    for idx, vv in enumerate(VV_i):
        if list(vv['order']) != sk['order']:
            continue
        if vv['qs'] != sk['qs']:
            continue
        if all(vv['side'].get(k) == s for k, s in sk['side'].items()):
            return idx
    return None

def main():
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    DELTA_VAL = 0.25
    lam = 1.0 / (n + DELTA_VAL)
    random.seed(2)
    ok_match = 0
    tot_viol_eq = tot_viol_nn = tot_viol_bound = 0
    for tr in range(trials):
        P = [(random.uniform(0, 10), random.uniform(0, 10))
             for _ in range(s)]
        sk = skel(P, n, lam)
        if any(v['kv'] > n - 1 for v in sk):
            continue
        VV = [gm.vertex_variants(v, sk[v]['kv'],
                                 tuple(x for x in range(s)
                                       if x != v), n)
              for v in range(s)]
        match = [find_variant(VV[i], sk[i]) for i in range(s)]
        if not all(isinstance(x, int) for x in match):
            print(f'trial {tr}: skeleton NOT matched '
                  f'(exponents {[v["kv"] for v in sk]})')
            continue
        ok_match += 1
        sol = [VV[i][match[i]] for i in range(s)]
        gm.ORIG.clear()
        b = gm.build_case(sol, n, 'A')
        vals = {'δ': DELTA_VAL}
        for i in range(s):
            for g in range(s - 1):
                vals[('r', i, g)] = \
                    sk[i]['gaps'][g] / lam - sk[i]['qs'][g]
        vio = {'eq': 0, 'nn': 0, 'bound': 0}
        for con in gm.ORIG:
            val = float(con.form.get(CONST := gm.CONST, 0))
            for k, c in con.form.items():
                if k == gm.CONST:
                    continue
                kk = 'δ' if k == gm.DELTA else k
                val += float(c) * vals.get(kk, 0.0)
            if con.is_eq:
                if abs(val) > 1e-6:
                    vio['eq'] += 1
            elif con.kind in ('ang',):
                if val > 1e-6:
                    vio['bound'] += 1
            elif val > 1e-6:
                vio['nn'] += 1
        tot_viol_eq += vio['eq']
        tot_viol_nn += vio['nn']
        tot_viol_bound += vio['bound']
        if any(vio.values()):
            print(f'trial {tr}: viol={vio} '
                  f'exponents={[v["kv"] for v in sk]}')
    print(f'\ns={s} n={n}: {ok_match}/{trials} matched, '
          f'eq viol={tot_viol_eq} nn viol={tot_viol_nn} '
          f'bound viol={tot_viol_bound}')

if __name__ == '__main__':
    main()
