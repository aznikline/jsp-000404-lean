"""Check LP status of the 'hard' (no-L1-gadget) skeletons found by
lane_a3 staged eval."""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import link_graph as lg
import residual_map as rm
from lane_a3 import stage_eval

n = s = 4
ks = json.loads(sys.argv[1])
limit = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
VV = ge.build_VV(ks, n, s)
sigvars = ge.build_sigvars(VV, s)
E = rm.load_g()
cnt = 0
hard = []
for sol, idxs, sigk in ge.gen_cases(ks, n, s, VV=VV, sigvars=sigvars):
    cnt += 1
    if cnt > limit:
        break
    sol = [dict(x) for x in sol]
    ctx = lg.Ctx(sol, n, s)
    st, best = stage_eval(ctx)
    if best is None or best['bound'] < F(1, 2):
        st_, lo = lg.lp_level(E, sol, n)
        hard.append((idxs, st_, str(lo),
                     None if best is None else str(best['bound'])))
print(f'leaves={cnt} hard={len(hard)}')
for h in hard:
    print(h)
