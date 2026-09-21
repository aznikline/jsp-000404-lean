"""Full-spectrum scan: for every deficit profile, per-skeleton min delta.

Tests the integer-level conjecture:  M* = max chain score is an
integer with M* <= 2*delta, so delta_min must land on
{0, 1/2, >=1} — and thresholds W>2, W>5/2 should force M*>=1, >=2.

Usage: python3 level_scan.py s4 [leaf_cap] [per_sig]
"""
import sys, json, itertools
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import generic_model as gm
import generic_cegis as gce


def scan_profile(ks, n, s, leaf_cap=30000, per_sig=100):
    """Enumerate skeletons; return {delta_min_str: count}."""
    VV = ge.build_VV(ks, n, s)
    sigvars = ge.build_sigvars(VV, s)
    reps = [{k: VV[i][idxs[0]] for k, idxs in sv.items()}
            for i, sv in enumerate(sigvars)]
    keys = [list(sv) for sv in sigvars]
    ch = [None] * s
    spec = {}
    leaves = sigs = 0
    tris = list(itertools.combinations(range(s), 3))

    def sig_run(v):
        nonlocal sigs, leaves
        for k in keys[v]:
            ch[v] = k
            if all(ge.consistent(ch, reps, s, v, u)
                   for u in range(v)):
                if v == s - 1:
                    sigs += 1
                    buckets = [sigvars[v2][ch[v2]] for v2 in range(s)]
                    cnt = 0
                    for sol_idx in itertools.product(*buckets):
                        cnt += 1
                        if cnt > per_sig or leaves > leaf_cap:
                            break
                        leaves += 1
                        sol = [VV[t][sol_idx[t]] for t in range(s)]
                        if not all(gm.tri_maybe(t, sol, n)
                                   for t in tris):
                            continue
                        gm.ORIG.clear()
                        b = gm.build_case(sol, n, 'A')
                        if b is None:
                            continue
                        ineqs, eqs = b
                        ineqs = gm.substitute(eqs, ineqs)
                        st, lo = gce.lp_min_delta_f(ineqs)
                        key = 'inf' if st != 'bounded' \
                            else str(F(lo).limit_denominator(96))
                        spec[key] = spec.get(key, 0) + 1
                else:
                    sig_run(v + 1)
            if leaves > leaf_cap:
                return
    sig_run(0)
    return spec, sigs, leaves


def main():
    s = int(sys.argv[1][1]) if len(sys.argv) > 1 else 4
    leaf_cap = int(sys.argv[2]) if len(sys.argv) > 2 else 30000
    per_sig = int(sys.argv[3]) if len(sys.argv) > 3 else 100
    n = s  # normalized problem: n = s? keep n param explicit
    if len(sys.argv) > 4:
        n = int(sys.argv[4])
    profs = gce.deficit_profiles(n, s, lo=-1, hi=99)
    out = []
    for d in profs:
        W = sum(F(1, 2) ** x for x in d)
        ks = [n - 1 - x for x in d]
        spec, sigs, leaves = scan_profile(ks, n, s, leaf_cap, per_sig)
        vals = sorted(spec, key=lambda x: (x == 'inf', float(F(x)) if x != 'inf' else 9))
        row = dict(deficit=d, ks=tuple(ks), W=str(W),
                   sigs=sigs, leaves=leaves, spectrum=spec)
        out.append(row)
        print(f"d={d} W={float(W):.4f} sigs={sigs} leaves={leaves} "
              f"spectrum={spec}", flush=True)
    fn = f'level_scan_s{s}.json'
    json.dump(out, open(fn, 'w'), indent=1)
    print(f'-> {fn}')


if __name__ == '__main__':
    main()
