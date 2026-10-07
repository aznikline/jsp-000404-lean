# LOW4 whole-band FixedCard entry audit

The whole-band counterexample entry is legitimate and already implemented. The new bridge can remove the separate FixedCard premise. It does not, by itself, remove the one possible second-deletion event at an original zero observer.

The audit is static. No Lean/Lake or Git was run. The new source is SOURCE_ONLY, not a kernel receipt. Its imported CriticalReduction has now separately passed locally at source `d0fdb06010c62be484d02f7731d63d3250536a88b31b5112bc4d33d683632968`.

## Existing quantified producers

`ActualMinimalBandCounterexample.Model.minimum_card` already quantifies every `r>=3`, every actual `d:Fin r -> Plane2`, and every `scale` with `rho<scale<=upper`. It compares all legal over-capacity configurations in that whole domain. It is not merely minimality at the current lambda.

`CounterCard` and `exists_minimal_counter` in ActualMinimalBandCounterexample explicitly implement the joint selection by `Nat.find`: existence of one legal over-capacity configuration in the band supplies the least N among ALL configurations and ALL band scales. `model_card_le_cap_succ` gives N<=17 for cap16. No new Nat.find or stronger Model definition is needed.

`exists_fixed_card_maximum` already performs a second attained maximum among all configurations/scales of that same N, using the independent coarse classical bound. `exists_low_fixed_card_critical_model` packages both selections for a LOW strip. For n4, applying the new actual critical reduction to its `.toModel` forces the selected maximum M=17. This is a direct existing-producer route.

## Short explicit new bridge

The new `ActualLowFourWholeBandFixedCard.model_fixed_card_seventeen` proves the required maximality for the existing original H without changing its point set:

1. CriticalReduction gives current potential=17.
2. Test an arbitrary same-cardinality legal configuration d at an arbitrary band scale.
3. If its potential<=16, it is certainly<=17.
4. Otherwise package d/scale into a Model with the SAME N and the existing whole-band `H.minimum_card`. That field's type is independent of H's particular c/lambda.
5. CriticalReduction forces that test model's potential=17.

Thus every test value is<=17, while the current original c/lambda attains17. This derives `FixedCardMaximal ... N 17`; it does not silently assume it. A model that only had fixed-lambda minimality would NOT support this argument.

The public `exists_whole_band_fixed_card_seventeen` starts from an actual legal over-capacity point configuration and band inequalities, reuses `exists_minimal_counter`, and returns a genuinely selected FixedCardModel17. It asserts no LOW4 capacity conclusion.

`smaller_card_capacity_at_any_band_scale` also makes the proper-subset statement explicit: for every r<N with r>=3, every legal r-point realization and every band scale has potential<=16. This is a capacity fact from minimality, not a license to construct a Model or maximum for that smaller realization.

## Existing plateau and closed-boundary consumers

Once FixedCardModel17 is genuinely produced, the checked existing functions are directly reusable:

- `actual_fixed_card_model_of_smaller_scale`: same original c is still a FixedCardModel17 at every rho<lambda'<=lambda.
- `actual_fixed_card_score_plateau`: current original potential and every original row score remain fixed.
- `actual_fixed_card_gap_score_plateau`: each ORIGINAL full cyclic gapScore remains fixed. Raw floors may still move0->1; no raw-floor plateau is asserted.
- `actual_fixed_card_gap_le_score_boundary`: each ORIGINAL full gap g satisfies `g <= (gapScore(lambda,g)+2)*rho`.
- `ActualF17ZeroDeletionBoundary.actual_low_four_zero_delete_gap_le_two_rho`: after deleting ONE original zero target, each original zero source's retained row has all gaps<=2rho. The deleted configuration is neither assumed critical nor maximal.

The new source wraps the last four interfaces so callers supply only the original whole-band Model. Smaller-scale legality follows from `lambda'<=lambda`, positive lambda' and the original triangle cap. Potential is nondecreasing as lambda decreases; maximality17 then makes it constant. Every scale used is strictly above rho. No row-score equality, flatness or sharp LOW capacity at rho is claimed.

## Twice-deleted physical outside gaps

For an ORIGINAL POSITIVE observer, DevinF17HullGap.actual_zero_pair_outside_gap_plateau_of_windows applies at every lower interior scale once both original zero targets and observer positivity are transported by the original score plateau. Its original outside gap is a genuine cyclic gap in the window's own nonzero reference; use reference invariance or repackage the whole-band Model at that reference to transport its gapScore plateau. A physical Window can be reused at lambda' by keeping all geometric fields and weakening only `width_le_legality`.

Let t=gapScore(lambda,E0) for the original outside E0. Then for every rho<lambda'<=lambda the typed plateau gives `E' < (t+2)*lambda'`, with that SAME t. If `E'>(t+2)*rho`, choose lambda' strictly between rho and min(lambda,E'/(t+2)); the two strict inequalities contradict each other. Therefore the correct closed endpoint result is `E' <= (t+2)*rho`. This positive-observer bridge has no remaining mathematical blocker, but its new wrapper is not yet implemented/compiled here.

For an ORIGINAL ZERO observer, the positive-score hypothesis is absent. The genuine zero-pair budget permits a unit gain at the second deletion. The present Selector theorem supplies only `E'<3*lambda'`, hence `E'<=3*rho`, and uniqueness of the possible boundary event. FixedCardMaximal at the ORIGINAL N does not imply maximality or plateau at N-2. It is invalid to apply the original full-gap boundary theorem directly to the new twice-deleted gap.

The exact rational ingredient check in JSP404_LOW4_FIXED_CARD_GAP_INGREDIENT_COUNTERCHECK_20261008.json illustrates this specific limitation. Normalize rho=1, pi=9/2, lambda=9/8. One actual-row-shaped circular list has wrap6/5 and inner gaps3/5,3/5,1,1/2,3/5. Its original and both single-deletion rows remain score zero throughout the open band, but deleting both first rays produces outside12/5>2rho, with permitted score one throughout. The original physical-window legality cap holds for this row. This is only a local gap example, NOT a coherent Section4 point configuration or a counterexample to additional global geometric restrictions.

## Remaining exact scope

The FixedCard extra premise can be removed legally at the whole-band contradiction entry, using existing selection plus the now-verified Phi17 reduction. Existing original-gap and single-zero-deletion boundary consumers can then be reused.

The still missing zero-observer argument must rule out or safely select around the allowed second-deletion event using additional original geometry/count information. It cannot be supplied by calling the N-2 subset a new maximal Model. No global LOW4 capacity or original arbitrary-N lower theorem is claimed by this audit.

New source: `Jsp000404/ActualLowFourWholeBandFixedCard.lean`.
Source SHA: bfbbc1abc02faa2cd473c83cab48f0548c429c006bda5b1163086d82a3fc99ea.
Candidate exports: model_fixed_card_seventeen, exists_whole_band_fixed_card_seventeen, smaller_card_capacity_at_any_band_scale, score_plateau, gap_score_plateau, original_gap_le_score_boundary, zero_delete_gap_le_two_rho.
