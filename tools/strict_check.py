"""Strict-remainder (r<1) checker layer.

Semantics: a skeleton is *strictly consistent* iff the mode-A system has a
solution with 0 <= r < 1 on every gap and 0 <= delta < 1.  This is decided
exactly by the margin LP: replace r<=1 / delta<=1 by r<=M / delta<=M (M>=0)
and minimize M.  min M < 1  <=>  strict feasibility (no epsilon needed).

For a strictly consistent skeleton, inf delta over the strict-feasible set
equals the closed-model delta_min: the strict set is the closed polytope
minus boundary faces, and convexity gives a sequence r<1, delta<1
approaching any boundary minimizer.  Levels in {0, 1/2, 1} therefore carry
over verbatim; only closed-'1' skeletons that are boundary-only collapse to
'inf' (they were never feasible in the domain delta<1 anyway).

API:
    strict_margin(sol, n) -> ('bounded'|'infeasible', minM or None)
    strict_level(sol, n)  -> Fraction in {0,1/2,1} or 'inf'
"""

import generic_model as gm
import residual_map as rm
from fractions import Fraction as F

E = rm.load_g()


def strict_margin(sol, n):
    gm.ORIG.clear()
    ineqs, eqs = gm.build_case(sol, n, 'A', strict=True)
    sub = gm.substitute(eqs, ineqs)
    st, mM, y = rm.glp_min_delta(sub, gm.CONST, gm.MARGIN)
    return st, mM


def closed_level(sol, n):
    gm.ORIG.clear()
    ineqs, eqs = gm.build_case(sol, n, 'A')
    sub = gm.substitute(eqs, ineqs)
    st, lo, y = rm.glp_min_delta(sub, gm.CONST, gm.DELTA)
    return st, lo


def strict_level(sol, n):
    """Strict-domain debt level: Fraction or 'inf'."""
    st, mM = strict_margin(sol, n)
    if st != 'bounded' or mM >= 1:
        return 'inf'
    st2, lo = closed_level(sol, n)
    if st2 != 'bounded':
        return 'inf'
    if lo >= 1:
        return 'inf'
    return lo
