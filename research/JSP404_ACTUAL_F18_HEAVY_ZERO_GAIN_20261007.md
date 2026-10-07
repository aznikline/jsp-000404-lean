# Original LOW heavy-observer zero gain, including F17 and F18

Status: SCOPED_PASS. Final source passed strict trust-zero and genuine
normal target build. All selected declarations use only standard three
axioms: propext, Classical.choice, and Quot.sound.

Source: `Jsp000404/ActualF18HeavyZeroGain.lean`.
Two selected exports are checked:

* actual_low_four_heavy_observer_gain_eq_zero;
* actual_heavy_observer_gain_eq_zero (the F18 specialization).

The general theorem takes the original actual n4 LOW minimum-counter
Model to cap 16, a nonzero reference, an original observer p of original
score two, and any distinct deleted target q. It concludes that the
actual gain of p's original row upon deleting q is zero. It does not
require original potential 18; it also applies to an original F17 model.
The F18 export is a thin specialization with its potential-18 argument
retained. Its proof no longer depends on the new Frame producer.

The general source internally derives the floor-four LOW strip. The
existing low_model_nonsaturated theorem excludes a saturated original
row, and the actual row-cell bound gives every original score at most
two. If the original model had only three points, the existing genuine
three-point LOW capacity would contradict its over-capacity field.
Thus at least four original points exist, providing the cardinality
needed to invoke the actual single-deletion cap. Neither an overall
score cap, a gain budget nor a cardinality cap is a caller premise.

A positive gain at the score-two observer would have weighted expense
at least four. Every target's original weight is at most four. The
existing checked certificate-A theorem removable_of_gain1_ge therefore
makes q actually removable. The original Model's checked
not_actual_removable gives the contradiction, using minimum original
counter-cardinality. This reuses the exact existing deletion/charge proof
rather than reimplementing the multiplicative ledger or transporting a
restrictionGain quantity to a rowGain quantity. The retained source is
p and the deleted target is q throughout; they are never interchanged.

The current HullSmallScoreTypes candidate has no singleton-to-rowGain
bridge. Its actual clump separation can support such a bridge with
rowGain_pos_of_forall_angle_ge, but the HM/HO clump-size consumers are not
added to this core leaf. They must use the actual internally produced
clumps and be checked separately.

Final verification validates the internally derived geometric and deletion
bridges described above. See the exact source and raw-output bindings in
the matching JSON receipt.

This source does not close full F17/F18 capacity, mixed-hull paper cases,
or the original arbitrary-N lower bound.

Final verification: strict trust-zero exited 0 in 69.79 seconds; genuine normal target build exited 0 in 61.73 seconds. Both guarded runs stayed below 8 GiB and 180 seconds, and the exact source remained unchanged. Selected declarations: 2. Own warnings: strict 0, normal 0. No failed attempts or source repairs occurred.

Final source SHA-256: 53991270c06ee2b0429905d2aacc8fdd6a27a20943558995d387e81da9e62d84.
