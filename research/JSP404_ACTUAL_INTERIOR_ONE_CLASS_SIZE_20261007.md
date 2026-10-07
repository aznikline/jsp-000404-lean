# Original actual class sizes and light deletion budgets

Status: SCOPED_PASS. Final source passed strict trust-zero and genuine
normal target build. All selected declarations use only standard three
axioms: propext, Classical.choice, and Quot.sound.

Source: `Jsp000404/ActualInteriorOneClassSize.lean`.
The frozen Partition, Runs and AngleGap modules are not edited.

The checked source uses the original n4 LOW minimal-counter Model and
potential 18. It internally selects an actual minimum-score point, applies
the existing critical form, and derives minimum score one. Consequently,
any original target q of score one is an actual minimum-score target;
the critical deletion theorem gives zero incoming original gains toward
q at every other original row.

At an original full-hull nonvertex p of score one, the source uses the
fixed `ActualInteriorOnePartition.actualPartition` of the original
configuration. If q had no distinct point in its class, the checked
`singleton_in_class_actual_gain` theorem would give a positive actual
gain at p. This contradicts q's original zero incoming gain. Thus every
light target has a distinct original companion in the same actual class.
In particular, each class consisting entirely of light points has at
least two members.

The stronger conclusion that all three classes have size at least two
requires zero gain toward every original target at the center. This
extra actual deletion condition is explicit in the general theorem.
Summing the three finite fibers then gives at least six other original
points, hence at least seven original points in total. Equality with six
other points is allowed. The immediate contradiction applies to at most
five other points (at most six original points), not to six other points.

The source deliberately does not infer this all-target condition from
the F18 light-only deletion condition. A singleton heavy class remains
allowed by the original budget; mixed-hull paper arguments explicitly
use such classes. No caller-supplied abstract classifier replaces the
actual producer. `members` only denotes a finite fiber of the producer's
Data output; all geometric conclusions use the original actualPartition.

The checked stronger metric witness stays inside the same actual
class. In the n4 LOW Model its angle at p is at most pi-4*lambda, which
is strictly below lambda/2. The checked metric comparison then gives
`dist(q,j) < dist(q,p)`, with the common endpoint q. This is useful with
the existing nearest-hull consumer and does not reverse a nearest-neighbor
inequality or extend the LOW half-scale conclusion to HIGH.

Eight selected declarations are checked:

* actual_low_four_F18_score_ge_one;
* actual_low_four_F18_light_incoming_gain_zero;
* actual_class_companion_of_zero_gain;
* actual_low_four_F18_light_class_companion;
* actual_low_four_F18_pure_light_class_card_ge_two;
* actual_interior_one_all_zero_class_card_ge_two;
* actual_interior_one_all_zero_card_ge_seven;
* actual_low_four_F18_light_class_closer.

Final verification validates these bridges. Source and raw-output hashes
are bound in the matching receipt.

This source does not close any full mixed-hull branch, full F17/F18
capacity, or the arbitrary-N original lower bound.

Final verification: strict trust-zero exited 0 in 35.42 seconds; genuine normal target build exited 0 in 66.27 seconds. Both guarded runs stayed below 8 GiB and 180 seconds, and the exact source remained unchanged. Selected declarations: 8. Own warnings: strict 0, normal 0. No failed attempts or source repairs occurred.

Final source SHA-256: 46cdc5d8ad4fb516a39d4db22695f64142026771f0881e8823ad08723e959ec3.
