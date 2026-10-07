# Actual outside-gap plateau after two original zero deletions (Devin, 2026-10-08)

Status: PARTIAL, scoped, kernel-checked. The original all-N theorem is OPEN and
`MainTheorem` lower N>=17 still has `sorryAx`. The F17 hull-zero selector
(existence of the pair of zero targets plus a surviving positive full-hull
observer, see JSP404_F17_HULL_ZERO_SELECTOR_AUDIT_OCT8.md) is NOT proved here.

Source: `Jsp000404/DevinF17HullGap.lean`, namespace `Jsp404.DevinF17HullGap`.
Receipt: `verification/devin-f17-hull-gap-20261008/RECEIPT.md`.

## Main statement

`actual_zero_pair_outside_gap_plateau` (hs : 3 <= s, e != 0):
original `ActualMinimalBandCounterexample.Model o e rho upper 16 (s+2) c lam`,
zero targets `p` and `p.succAbove q` (distinct by construction,
`targets_and_observer_distinct`), surviving observer `A = p.succAbove (q.succAbove a)`
with `0 < rowScore lam (directionRow o e c A)` and `IsHullVertex c A` (original full hull).
Conclusion: original potential is 17, and there exist actual hull Windows
`W` (original configuration at `A`) and `W'` (configuration `(c ∘ p.succAbove) ∘ q.succAbove`
at `a`), both produced internally by `exists_actual_hull_ray_window`, such that with
`t = gapScore lam (pi - W.width)` and `E = pi - W'.width`:

    gapScore lam E = t,   pi - W.width <= E,   E < (t + 2) * lam.

`actual_zero_pair_outside_gap_plateau_of_windows` proves the same for every pair of
actual Windows (no hull hypothesis needed once Windows are given).

Only the caller's reference `e != 0` is an extra non-degeneracy premise (needed to
move scores between the `e` chart and the Window chart via
`rowScore_directionRow_reference_eq`). No gap budget, score bound, synthetic class
or restricted minimum-counter Model is supplied.

## Proof route

1. Budgets from the ORIGINAL `H` only: `actual_minimum_score_critical_form` gives zero
   first-deletion change of the observer score; `actual_zero_pair_deletion_budget`
   (positive original score => zero second-deletion gain) plus
   `rowScore_le_of_sublist` gives zero second-step change. Both are transported to
   the Window chart `W.base`.
2. Chart: `dirRep_window`, and `row_pairwise_lt` (legality excludes two centers on a
   ray, so the chart row is strictly increasing).
3. `theta_transport`: restricted Window coordinates equal original coordinates minus
   the original coordinate of the restricted left boundary ray (oriented-angle
   addition plus `toReal` range). Hence `row_wrap`: in the original chart, the
   retained row's wrap gap equals the physical outside gap `pi - W'.width`
   (and `pi - W.width` for the original row).
4. `wrap_step` (pure lists): erasing one actual ray with zero row-score change keeps
   the wrap gap from shrinking and keeps its score. Endpoint erasure merges the
   outside gap (>= lam) with the adjacent internal gap, so zero merge gain forces the
   internal gap < lam and the score unchanged; interior erasure leaves it fixed.
   Physical deletions are actual erasures by `erase_directionRow`.
5. `isHullVertex_restrict`: retained original extreme points stay extreme in the
   subconfiguration (used only to build `W'`; new subset hull vertices are never
   assumed to be original).
6. Floor arithmetic: `gapScore = floor(E/lam) - 1 = t` and `floor >= 1` give
   `E < (t+2) lam`.

Not covered: the selector existence; any statement about FixedCard closed bounds;
the regular heptagon and F16 SAT controls are untouched.
