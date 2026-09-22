"""Exact Farkas certificate for delta>=1 on a chosen skeleton of an
arbitrary profile (generic model).  Prints the ORIG constraints with
dual weights.
"""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_model as gm
import generic_enum as ge
import generic_cegis as gce

N = S = 4


def main():
    ks = [int(x) for x in sys.argv[1:5]]
    idxs = [int(x) for x in sys.argv[5:9]]
    VV = ge.build_VV(ks, N, S)
    sol = [VV[i][idxs[i]] for i in range(4)]
    for i in range(4):
        vv = sol[i]
        print(f'v{i}: order={vv["order"]} bits='
              f'{dict(sorted(vv["bits"].items()))} qs={vv["qs"]}')
    gm.ORIG.clear()
    b = gm.build_case(sol, N, 'A')
    ineqs, eqs = b
    ineqs = gm.substitute(eqs, ineqs)
    st, lo, y = lp_min_delta_exact(ineqs)
    print(f'exact LP: {st} min delta = {lo}')
    if st != 'bounded':
        return
    out = extract(ineqs, y)
    print('certificate:')
    for cid, w in sorted(out[0].items()):
        if w:
            print(f'  {w} x [{gm.ORIG[cid].desc}]')


def lp_min_delta_exact(ineqs):
    """Exact min-delta via Fraction LP: reuse generic_model + a small
    exact solver.  We reuse remainder_check.lp_min_delta by converting
    variable names: our vars are ('r',i,g) tuples already."""
    import remainder_check as rc
    return rc.lp_min_delta(ineqs)


def extract(ineqs, y):
    return gm.extract_cert(ineqs, y)


if __name__ == '__main__':
    main()
