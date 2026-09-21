"""Soundness check v2: for a REAL 4-point configuration, compute each
vertex's real exponent kv = Σ(floor(gap/λ)−1)+, build the variant list
with THAT exponent, find the real skeleton inside, then evaluate every
ORIG constraint numerically with the true remainders.

All ORIG constraints must hold.  If any fails → model bug.
"""
import sys, math, random, importlib.util
spec = importlib.util.spec_from_file_location(
    'rc', 'tools/remainder_check.py')
rc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rc)

n = rc.N
DELTA_VAL = 0.25
lam = 1.0 / (n + DELTA_VAL)

def skel(P):
    V = []
    for i in range(4):
        dirs = {j: math.atan2(P[j][1] - P[i][1], P[j][0] - P[i][0])
                % math.pi for j in range(4) if j != i}
        order = sorted(dirs, key=lambda j: dirs[j])
        angs = [dirs[j] for j in order]
        gaps = [((angs[(t + 1) % 3] - angs[t]) % math.pi) / math.pi
                for t in range(3)]
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
        V.append(dict(order=order, gaps=gaps, qs=qs, side=side, kv=kv))
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

random.seed(2)
P = [(random.uniform(0, 10), random.uniform(0, 10)) for _ in range(4)]
sk = skel(P)
print('real exponents:', [s['kv'] for s in sk])
VV = [rc.vertex_variants(v, sk[v]['kv'],
                          tuple(x for x in range(4) if x != v), n)
      for v in range(4)]
match = [find_variant(VV[i], sk[i]) for i in range(4)]
for i in range(4):
    print(f'v{i}: order={sk[i]["order"]} qs={sk[i]["qs"]} '
          f'kv={sk[i]["kv"]} -> variant {match[i]}')
if not all(isinstance(m, int) for m in match):
    print('skeleton not matched')
    sys.exit(0)

sol = [VV[i][match[i]] for i in range(4)]
for mode in ('A', 'B'):
    rc.ORIG.clear()
    built = rc.build_case(sol, n, mode)
    if built is None:
        print(f'mode {mode}: build_case None on real skeleton — '
              'edge-side pairing inconsistency?')
        continue
    vals = {'δ': DELTA_VAL}
    for i in range(4):
        for g in range(3):
            vals[('r', i, g)] = sk[i]['gaps'][g] / lam - sk[i]['qs'][g]
    bad = 0
    for desc, form, is_eq in rc.ORIG:
        s = float(form.get(rc.CONST, 0))
        for k, c in form.items():
            if k == rc.CONST:
                continue
            kk = 'δ' if k == rc.DELTA else k
            v = vals.get(kk)
            if v is None:
                continue
            s += float(c) * v
        if is_eq and abs(s) > 1e-6:
            print(f'  VIOLATED eq [{desc}] = {s:.6f}')
            bad += 1
        elif not is_eq and s > 1e-6:
            print(f'  VIOLATED ineq [{desc}] = {s:.6f}')
            bad += 1
    print(f'mode {mode}: {bad} violations over {len(rc.ORIG)} '
          'constraints')
