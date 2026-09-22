"""Boundary study: W<=2 profiles; consistent skeletons with delta_min=0
(no positive gadget). Dump their structure."""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import link_graph as lg
import residual_map as rm
from lane_a import profile_data

n = s = 4
ks = json.loads(sys.argv[1])
limit = int(sys.argv[2]) if len(sys.argv) > 2 else 10
cap = int(sys.argv[3]) if len(sys.argv) > 3 else 200000
VV = ge.build_VV(ks, n, s)
sigvars = ge.build_sigvars(VV, s)
E = rm.load_g()
cnt = 0
found = 0
for sol, idxs, sigk in ge.gen_cases(ks, n, s, VV=VV, sigvars=sigvars):
    cnt += 1
    sol = [dict(x) for x in sol]
    st_, lo = lg.lp_level(E, sol, n)
    if st_ == 'bounded' and lo == 0:
        found += 1
        if found <= limit:
            pd = profile_data(sol, n, s)
            print(f'=== idxs={idxs} sigk={sigk}')
            for v, p in enumerate(pd):
                print(f'   v{v} B={p["B"]} nz={p["nz"]} d={p["d"]} '
                      f'K={p["K"]} qs={p["qs"]} bits={p["bits"]} '
                      f'ord={p["order"]}')
    if cnt >= cap:
        break
print(f'leaves={cnt} delta0={found}')
