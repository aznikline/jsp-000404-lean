# Actual full-hull physical ray window

As of 2026-10-07 UTC: **READY — genuine strict and normal compiler PASS.**
Final strict attempt 2 (`--trust=0 -M8000`) and the genuine own-module Lake
build both exited 0. All three printed declarations use exactly `propext`,
`Classical.choice`, and `Quot.sound`; final source warnings are zero.
The first strict run also passed, with four style warnings on its prior
source. Its actual source snapshot and original stdout are retained; it is
not a failed run and is not bound to the final source. The normal build
replayed 186 old dependency warnings, none from this module.

The new source is `Jsp000404/ActualHullRayWindow.lean`. Its public producer
`Jsp404.ActualHullRayWindow.exists_actual_hull_ray_window` takes an orientation,
`3 ≤ s`, original `Section4Legality c lam`, an original index `p`, and
`IsHullVertex c p` for the convex hull of **all original centers**.

The output is a `Window` containing two distinct actual indices `a,b ≠ p`,
the actual base ray `c a - c p ≠ 0`, a width `0 < alpha < pi`, and real
coordinates for all original indices other than `p`. Their real coordinates
lie in `[0,alpha]`, their oriented angles from the base are exactly these
coordinates modulo `2*pi`, and the boundary coordinates are `theta a = 0`
and `theta b = alpha`. The width is the actual angle `angle (c a) (c p) (c b)`
and is at most `pi - lam` by original legality.

The caller supplies no supporting normal, angular array, cone, selected-hull
replacement, capacity inequality, or desired conclusion. The construction
first uses the full-hull extreme-point characterization to exclude the hull
of the other original points. Finite-hull closure and strict Hahn–Banach
separation then produce an inward normal through the real Riesz equivalence.
Every actual ray has strictly positive inner product with this normal. Its
principal signed angle therefore lies in `(-pi/2,pi/2)`. Actual finite
minimum and maximum signed angles produce the two endpoints. Differences
remain strictly between `-pi` and `pi`; thus no wrapping assumption or
`alpha < pi/2` restriction is needed. A third legal original point makes
the span positive.

The two additional public helpers are
`not_mem_hull_others_of_isHullVertex` and
`exists_strict_supporting_normal`. The latter needs only injectivity,
full-hull vertex membership, and `2 ≤ s`.

## Budget consumer

The existing `exists_inward_bisector_of_ray_window` accepts a physical
window of any width below `pi`. It can consume this new actual window.
For an injective selection of actual hull vertices, the existing
`PositiveRowCount.actual_bisector_turn_budget` gives
`sum (pi - alpha_p) ≤ 2*pi`, using the actual opposing rays between every
two selected centers and the already checked weighted circle-separation
theorem. If actual hull-type producers subsequently prove
`alpha_p ≤ pi - k_p*lam`, this yields `sum k_p * lam ≤ 2*pi` and hence
`sum k_p ≤ 8` when `2*pi/9 < lam`. The separate new module
`ActualHullTurnBudget.lean` has now genuinely checked this scoped consumer
with three more standard-axiom declarations.

This avoids requiring cyclic hull adjacency, a polygon exterior-angle sum,
or replicated normal directions. The type-specific stronger caps, the
complete F18 exclusion, F17, other HIGH configurations, and the original
arbitrary-N theorem remain separate open kernel obligations.
