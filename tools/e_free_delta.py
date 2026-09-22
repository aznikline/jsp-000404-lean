"""Lane E repro — negative-delta mode-A feasibility.

Lean's `ModeA` (Jsp000404/Gadget.lean) has NO explicit hypothesis
0 <= delta < 1; the operational checker adds those bounds.  This
script shows:

  1. a skeleton feasible at delta = -1/2 under free-delta ModeA
     semantics (capped LP reports min delta = 0, hiding the
     negative-feasible region);
  2. enumerate_max returns gadget bound -1/2 — exactly the free-LP
     minimum, i.e. the evaluator is tight even below delta = 0;
  3. negative-delta feasibility was only ever observed in W <= 2
     profiles (140k sampled s=4 variant tuples, 1572 free-feasible,
     0 suspects with W>2 and free-min < 1/2).

Caveat demonstrated here: `generic_cegis.lp_min_delta_f` passes
bounds [(0,1)] per variable to seidel_lp.lp_max, silently clamping
delta to [0,1] even when the 'delta<1'/'delta>=0' constraints are
skipped.  Use lane_e_util.lp_min_delta_free (bounds=None) instead.

Run:  python3 tools/e_free_delta.py
"""
import sys
sys.path.insert(0, 'tools')
sys.path.insert(0, '.')
import lane_e_util as le

n = s = 4
d = (1, 2, 2, 2)          # W = 5/4 (low band)
ks = le.ks_of_d(n, d)
idxs = (0, 36, 12, 0)

VV = le.ge.build_VV(ks, n, s)
sol = [VV[v][i] for v, i in enumerate(idxs)]

print('profile d=%s  W=%s  ks=%s  idxs=%s' % (d, le.W_of_d(d), ks, idxs))
for v, vv in enumerate(sol):
    print('  v%d order=%s bits=%s qs=%s'
          % (v, vv['order'], vv['bits'], vv['qs']))

print('\ncapped LP  (0<=delta<1):', le.lp_x(sol, n))
print('relaxed LP (delta>=0)  :', le.lp_relaxed(sol, n)[:2])
print('free LP    (any delta) :', le.lp_f_free(sol, n))

# demonstrate the bounds bug in generic_cegis.lp_min_delta_f
import generic_model as gm
import generic_cegis as gce
gm.ORIG.clear()
b = gm.build_case(sol, n, 'A', skip={'δ<1', 'δ≥0'})
ineqs, eqs = b
ineqs = gm.substitute(eqs, ineqs)
print('\nBUG DEMO — same free system through lp_min_delta_f '
      '(delta silently clamped to [0,1]):', gce.lp_min_delta_f(ineqs))

best = le.lg.enumerate_max(sol, n, s)
print('\nenumerate_max best bound:', None if best is None else best['bound'])
