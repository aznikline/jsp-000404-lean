"""Exact re-verification of scan survivors.

Usage: python3 tools/exact_verify.py MODE idx0 idx1 idx2 idx3 [--json]
where the four indices are variant indices into the VV lists for
ks = [3,2,2,1] (as printed by scan_profile.py 'lowest' lines).
Runs the exact Fraction simplex, prints min δ and the Farkas
certificate (combination of ORIG constraints giving δ ≥ min).
--json emits a machine-readable provenance record instead.
"""
import sys, json, importlib.util
spec = importlib.util.spec_from_file_location(
    'rc', 'tools/remainder_check.py')
rc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rc)

n = rc.N
ks = [3, 2, 2, 1]

def classify(desc, is_eq):
    """Constraint provenance class — used to audit that no mode-B-only
    assumptions leaked into a mode-A certificate."""
    if desc.startswith('V') and 'Σgap' in desc:
        return 'fan_sum'
    if desc.startswith('Δ'):
        return 'triangle_sum'
    if '≤π−λ' in desc:
        return 'tri_angle'      # Section4Legality.triAngle (provable)
    if '≥λ' in desc:
        return 'angle_lower'    # MODE-B ONLY — not derivable from GA
    if desc.startswith('f') and ('lo' in desc or 'hi' in desc):
        return 'facing'         # MODE-B ONLY — facing min-gap window
    if '≥0' in desc or '≤1' in desc:
        return 'nonneg'
    if desc.startswith('δ'):
        return 'delta_bound'
    return 'other'

def main():
    args = [a for a in sys.argv[1:] if a != '--json']
    want_json = '--json' in sys.argv[1:]
    mode = args[0]
    idxs = [int(x) for x in args[1:5]]
    VV = [rc.vertex_variants(v, ks[v],
                              tuple(x for x in range(4) if x != v), n)
          for v in range(4)]
    sol = [VV[i][idxs[i]] for i in range(4)]
    for i in range(4):
        vv = sol[i]
        print(f'v{i}: order={vv["order"]} bits={vv["bits"]} '
              f'qs={vv["qs"]}')
    rc.ORIG.clear()
    b = rc.build_case(sol, n, mode)
    if b is None:
        print('build_case None (edge pairing inconsistent)')
        return
    ineqs, eqs = b
    sub = rc.substitute(eqs, ineqs)
    res = rc.lp_min_delta(sub)
    if res[0] != 'bounded':
        print('exact LP:', res[0])
        return
    lo, y = res[1], res[2]
    print(f'exact LP: min δ = {lo}  (={float(lo):.4f})')
    out = rc.extract_cert(sub, y)
    if out is None:
        print('cert extraction FAILED')
        return
    W, combo = out
    ok = (combo.get(rc.DELTA, 0) == -1
          and all(v >= 0 for k, v in combo.items()
                  if k not in (rc.CONST, rc.DELTA))
          and combo.get(rc.CONST, 0) == lo)
    if want_json:
        record = {
            'mode': mode,
            'profile': ks,
            'variant_idxs': idxs,
            'min_delta': str(lo),
            'valid': bool(ok),
            'constraints': [
                {
                    'orig_id': cid,
                    'desc': rc.ORIG[cid][0],
                    'kind': classify(rc.ORIG[cid][0], rc.ORIG[cid][2]),
                    'is_eq': bool(rc.ORIG[cid][2]),
                    'coeff': str(w),
                }
                for cid, w in sorted(W.items()) if w
            ],
            'combined': {
                'const': str(combo.get(rc.CONST, 0)),
                'delta_coeff': str(combo.get(rc.DELTA, 0)),
                'remainder_terms': [
                    {'var': str(k), 'coeff': str(v)}
                    for k, v in combo.items()
                    if k not in (rc.CONST, rc.DELTA) and v
                ],
            },
        }
        # audit flag: a mode-A cert must never reference mode-B-only kinds
        bad = [c for c in record['constraints']
               if c['kind'] in ('angle_lower', 'facing')]
        record['mode_b_leak'] = bool(bad)
        print(json.dumps(record, indent=1, ensure_ascii=False))
        return
    print(f'certificate for δ ≥ {lo}:')
    for cid, w in sorted(W.items()):
        if w:
            print(f'   {w} × [{rc.ORIG[cid][0]}]')
    print('combined form:',
          {str(k): v for k, v in combo.items() if v})
    # sanity: combined form should equal  lo − δ
    # valid iff δ-coeff = -1, const = lo, and all r-coeffs ≥ 0
    # (then δ ≥ lo + Σ a_i r_i ≥ lo since r_i ≥ 0)
    print('cert valid (δ ≥ lo + Σa_i r_i, a_i ≥ 0):', ok)

if __name__ == '__main__':
    main()
