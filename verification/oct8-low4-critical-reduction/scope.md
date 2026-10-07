# Original n4 LOW minimal counter: potential 17 reduction

Status: SCOPED_PASS_ACTUAL_N4_LOW_CRITICAL_REDUCTION. Final strict trust-zero and genuine target-only normal checks passed on the same source. The selected declaration prints only `propext`, `Classical.choice`, and `Quot.sound` in both successful logs.

Source: `Jsp000404/ActualN4LowCriticalReduction.lean` (77 lines).
SHA-256: `d0fdb06010c62be484d02f7731d63d3250536a88b31b5112bc4d33d683632968`.
Selected declaration: `Jsp404.ActualN4LowCriticalReduction.actual_n4_low_model_potential_eq_seventeen`.

The public inputs are the original actual minimal counterexample Model with n=4 LOW band, sharp cap 16, an orientation, reference and its nonzero proof. Original cardinality is arbitrary. No potential value, minimum-score witness, saturation exclusion, score bound, deletion certificate or capacity premise is supplied by the caller. The conclusion is that the original actual potential equals 17.

The true `GlobalFiveLowCapacity.potential_le_two_pow_of_le_five_low` bound excludes original cardinality at most 5, because it supplies the LOW cap 16 and the Model is over cap 16. Hence the original point count is at least 6. This is not the HIGH cap 20. The original LOW nonsaturation theorem and actual row-cell/defect identities bound every original score by 2. A real minimum-score point is then chosen internally using `Finite.exists_min`; the verified LOW minimum-score critical form derives its own cap divisibility and gives original potential `16 + 2^minimumScore`.

Minimum score 0 gives 17. Minimum score 1 gives 18, contradicted by the verified whole F18 consumer. Minimum score 2 makes every original score exactly 2, so the original potential is four times the original cardinality; the critical form gives 20, forcing cardinality 5 and contradicting the internally proved count at least 6. No subset scores, subset Model or subset hull facts are used, and no circular dependency on this new reduction exists.

Final strict attempt 2 exited zero in 43.14 real seconds (guard 43.173), maximum process RSS 5151227904 bytes and process-group RSS 5457215488 bytes. Genuine normal attempt 1 exited zero in 64.42 real seconds (guard 64.656), maximum process RSS 4760977408 bytes and process-group RSS 5238718464 bytes. Normal built the own target and completed 9065 jobs. Both final checks have zero own-source warnings; inherited normal headers are counted in the receipt. Both 8 GiB / 180 second guards stayed clear and both snapshots match the final source. Sole compute was returned to Root immediately after the normal process exited, before preparing this receipt.

First strict attempt 1 genuinely failed only because the restricted simplifier left `16+1` instead of the target numeral 17 in the zero branch. Replacing that one `simpa only` with `simpa [h0]` normalized the constant. No mathematical premise, result or public interface changed. Its exact original aa0f source and raw log are retained as attempt 1; failed-log placeholder `sorryAx` output is not passing evidence.

This is a necessary reduction for the original counter-model. It does not exclude the remaining potential 17 case, prove unconditional n4 LOW capacity, or complete the original arbitrary-N sharp lower bound. The frozen source header records its preparation phase; this scope record and receipt record completed verification.
