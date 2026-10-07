# Actual F18 three-heavy acute consumers

2026-10-07 UTC: **READY — genuine strict and normal compiler PASS.**
New owned source: `Jsp000404/ActualF18ThreeHeavyAcute.lean`.
Old PASS sources, root imports, audit, status, Git and the index were not
modified.
Strict attempt 1 (`--trust=0 -M8000`) and genuine own-target normal attempt 1
exited 0 in 13.780 and 36.546 seconds. Both selected declarations use exactly
`propext`, `Classical.choice`, and `Quot.sound`; own warning counts are zero.
Neither the 8 GiB nor 180 s guard fired. No failed compiler runs occurred.

## First final subcase: no original hull light

The checked export `actual_F18_three_heavy_no_hull_light_false` takes the
original actual LOW `Model` cap16, original potential18, original heavy count
three, and the genuine geometric case condition that every original light
point is a full-hull nonvertex. It accepts no nearest-neighbor map, type
array, cone, circle budget, or desired capacity conclusion.

The internal original `ActualF18Frame` gives exactly three light points and
six original centers. The source selects those three actual light indices
and calls the already checked
`exists_actual_low_four_F18_light_nearest_full_hull` for each. This internally
chooses a weak nearest neighbor among all original points and proves its
original full-hull membership, retaining distance ties.

Because the current case has no original hull light, each chosen receiver
is heavy. Its actual `HeavyKind` is produced from the original configuration.
HM or HO supplies an actual pair of window-boundary rays with angle at least
`2*lambda`; the checked nonacute-heavy nearest-exclusion theorem rules out
that receiver. Each receiver therefore has an internally produced acute HA
window of width at most `pi-3*lambda < pi/3`.

Two distinct light targets cannot share one such receiver: the checked
`actual_nearest_indices_eq_of_small_anchor_angle` would identify them. Thus
the three internally chosen receivers are distinct original full-hull
vertices. For every actual pair of rays at each receiver, its genuine window
gives angle at most `pi-3*lambda`.

Finally, `selected_hull_integer_budget_le_eight` is applied to those three
actual receivers with constant natural weight three. Its geometric cap
premise is derived from the windows inside this proof; its total integer
budget is not a caller premise. It yields `3+3+3<=8`, a contradiction.

All hull predicates, scores, nearest comparisons, and point indices remain
on the original configuration. No subset hull or deleted critical model is
introduced. This is the `t=3,N=6,h=3` final subcase, not the entire F18 branch.

## At least one acute heavy in the whole t=3 branch

The second checked export `actual_F18_three_heavy_exists_acute_window`
internally selects all three original heavy indices. If none has an HA
window, the original `HeavyKind` producer makes each HM or HO and supplies
an actual angle at least `2*lambda`. The checked
`no_three_nonacute_heavy` then contradicts the original Model.

This supplies the actual acute-window witness, including its outside gap
score exactly two, needed to remove all `a=0`
three-heavy cases before addressing the remaining hull-light branches.
It does not assume a type assignment or a global count of acute vertices.

## Reused checked APIs and static validation risks

- `ActualF18Frame.actual_f18_frame` and the original `lightIndices` /
  `heavyIndices` finite sets.
- `ActualInteriorOneRuns.exists_actual_low_four_F18_light_nearest_full_hull`.
- `ActualHullSmallScoreTypes.exists_actual_hull_two_type`, including genuine
  actual window-boundary witnesses.
- `ActualHeavyNearestExclusion.actual_nonacute_heavy_not_weak_nearest`.
- `SharpNearestGeometry.actual_nearest_indices_eq_of_small_anchor_angle`.
- `ActualMixedRigidCardinality.actual_window_angle_le_width`.
- `ActualHullTurnBudget.selected_hull_integer_budget_le_eight`.
- `ActualNoThreeNonacuteHeavy.no_three_nonacute_heavy`.

The whole-source checks validated the finite `orderIsoOfFin` selection,
dependent `choose` for each actual receiver window, and transport of the weak
nearest statement when two receiver indices are equated. An independent
read-only source review by `window_api_audit` also found no mathematical or
API mismatch before compilation. A composed root audit remains a separate
integration check.

## Exact remaining t=3 consumers

The frozen mixed-hull PAPER note still supplies the `h=4,5,6` arguments with
at least one HA. Existing NoThree now removes its all-nonacute (`a=0`) cases,
including the old three-HM deletion/four-point matching route. Remaining
typed work includes the original hull/type-count classification, nearest
isolation in HO clumps, and the actual score-growth bridge when two original
light points clear a retained heavy clump. The proper-subset weighted budget
itself is already checked; the geometric growth must still be produced from
the real original deletion. No paper assertion is accepted as a formal
capacity hypothesis. Full t=3, full F18/F17, and the original arbitrary-N
theorem remain open.
