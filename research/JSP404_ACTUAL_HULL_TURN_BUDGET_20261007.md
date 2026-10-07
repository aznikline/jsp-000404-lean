# Actual selected full-hull turn budgets

As of 2026-10-07 UTC: **READY — genuine strict and normal compiler PASS.**
This module and its new `ActualHullRayWindow` dependency have each passed
whole-source strict validation with `--trust=0 -M8000` and a genuine own
Lake target build. All three declarations here use exactly `propext`,
`Classical.choice`, and `Quot.sound`. This module has zero own warnings;
old dependency diagnostics in the normal build are separately counted in
the receipt. There were no failed runs for this module.

`Jsp000404/ActualHullTurnBudget.lean` adds three checked public interfaces:

1. `exists_selected_hull_turn_budget`: given original Section-4 legality,
   `3 ≤ s`, an injective `pick : Fin r → Fin s`, `2 ≤ r`, and full original
   hull membership for every `pick i`, it internally chooses each actual
   window and proves `sum_i (pi - width_i) ≤ 2*pi` through the already
   checked `PositiveRowCount.turn_budget_of_ray_windows`. The coordinates
   are restricted to the selected original points; full-hull membership
   is measured in the original configuration throughout.
2. `selected_hull_card_le_eight`: if `2*pi/9 < lam`, every such injective
   selected family has at most eight entries. The cases with fewer than
   two selected entries are handled directly. For larger families, each
   actual window costs at least `lam` in the turn budget.
3. `selected_hull_integer_budget_le_eight`: for `2 ≤ r`, natural weights
   `k_i`, and explicit original geometric angle caps
   `angle(c a, c(pick i), c b) ≤ pi - k_i*lam` for all original distinct
   `a,b ≠ pick i`, instantiate the cap at the actual window's two distinct
   endpoint witnesses. This yields both `(sum_i k_i)*lam ≤ 2*pi` and
   `sum_i k_i ≤ 8` when `2*pi/9 < lam`.

The first two interfaces have no caller-supplied normal, cone, coordinate
array, or capacity bound. The third interface deliberately retains its
stronger **actual geometric angle cap** as a premise to be supplied by
future hull-type producers. It assumes neither its resulting integer
budget nor any total capacity, exclusion, or cardinality conclusion.

The internal circle argument uses actual opposing rays between selected
vertices, real inward bisectors, and weighted angular separation. It needs
neither cyclic convex-hull adjacency nor a formal polygon exterior-angle
sum. This does not complete the type-specific F18 caps, the entire F18/F17
exclusions, other HIGH configurations, or the original arbitrary-N theorem.
