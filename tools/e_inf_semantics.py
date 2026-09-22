"""Lane E repro — 'inf' is NOT always structural inconsistency.

Handoff claim challenged: capped-LP 'inf' was believed to mean the
skeleton is structurally inconsistent for all delta.  This script
shows a concrete s=4 skeleton that is infeasible under the capped
model (0 <= delta < 1) but feasible at delta = 2 under the relaxed
model (delta >= 0 only) — i.e. 'inf' can hide a high-debt skeleton,
and the gadget enumerator still certifies the exact bound.

Run:  python3 tools/e_inf_semantics.py
"""
import sys
sys.path.insert(0, 'tools')
sys.path.insert(0, '.')
import lane_e_util as le

n = s = 4
d = (1, 1, 1, 1)          # W = 4 * 1/2 = 2  (boundary)
ks = le.ks_of_d(n, d)     # [2, 2, 2, 2]
idxs = (0, 43, 16, 1)

VV = le.ge.build_VV(ks, n, s)
sol = [VV[v][i] for v, i in enumerate(idxs)]

print('profile d=%s  W=%s  ks=%s  idxs=%s' % (d, le.W_of_d(d), ks, idxs))
for v, vv in enumerate(sol):
    print('  v%d order=%s bits=%s qs=%s'
          % (v, vv['order'], vv['bits'], vv['qs']))

print('\ncapped LP  (0<=delta<1):', le.lp_x(sol, n))
print('relaxed LP (delta>=0)  :', le.lp_relaxed(sol, n)[:2])
print('free LP    (any delta) :', le.lp_f_free(sol, n))

best = le.lg.enumerate_max(sol, n, s)
print('\nenumerate_max best bound:', None if best is None else best['bound'])
if best is not None:
    print('  level M =', best['M'], ' pivot =', best['pivot'])
