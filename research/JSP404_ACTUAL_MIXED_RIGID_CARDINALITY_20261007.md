# Mixed actual rigid selection cardinality

Status: SCOPED_PASS. Final source passed strict trust-zero and genuine
normal target build. All selected declarations use only standard three
axioms: propext, Classical.choice, and Quot.sound.

Source: `Jsp000404/ActualMixedRigidCardinality.lean`.

The main checked theorem takes an original legal n4 LOW configuration,
with 2*pi/9 < lambda <= pi/4, a nonzero reference, and an injective selection
pick:Fin r -> Fin s. Each selected original center is either an original
full-hull nonvertex of original score one, or has original score two and
an actual original pair of distinct noncentral rays making an angle at
least 2*lambda. It proves r <= 4. No F18 Model is needed.

The heavy input is an actual original geometric witness, not an abstract
rigidity or class certificate. The source internally derives floor four,
then score two and the actual row-cell bound imply defect at most two.
The existing FullHullInteriorDefect theorem supplies membership in the
full original hull. The existing HullSmallScoreTypes producer then
internally selects a physical Window and one of HA/HM/HO.

A new public support lemma proves that every pair of original rays in
such a Window has actual angle at most its width. Its proof uses the
public actual_direction, theta_mem, base_ne_zero and width_lt_pi fields,
not the Types module's generated private names. The angle difference
lies inside the principal interval because the physical width is below
pi. HA has width <= pi-3*lambda < 2*lambda in this LOW range, contradicting
the supplied actual large-angle witness. HM and HO produce actual clumps;
same-class angles are at most R=pi-4*lambda, and different-class angles
are at least 2*lambda (HO gives the stronger 3*lambda).

At original interior score-one centers, the frozen actual AngleGap
producer supplies the same dichotomy on all original rays. Thus every
triangle of the selected original points has the dichotomy. The source
restricts actual legality and these physical angle facts to c composed
with pick, and invokes the checked ActualRigidCardinality theorem to get
r <= 4. It never treats a selected subset hull or selected subset score
as the original hull or original score. Small r is handled arithmetically;
the nontrivial branch derives the needed original cardinality from
injectivity, so no cardinality or rigidity cap is a caller premise.

Three selected declarations are checked:

* actual_window_angle_le_width;
* actual_heavy_large_angle_gap;
* actual_mixed_rigid_card_le_four.

Independent read-only review found no specific mathematics or API error.
Strict checking and the genuine normal build validated the Types
dependency, its Nonempty Sigma/HeavyKind elimination, the low-strip floor
inference, and the final restriction and physical-angle elaboration. All
three axiom reports contain only the standard three axioms. No admissions,
acceptance tables, caller classes, caller angle-gap conclusions or desired
capacity fields are introduced. Existing sources were not edited.

This checked theorem is a mixed rigid cardinality step, not a complete
F17/F18 capacity proof or an arbitrary-N original lower bound.

Final verification: strict trust-zero exited 0 in 55.25 seconds; genuine normal target build exited 0 in 50.97 seconds. Both guarded runs stayed below 8 GiB and 180 seconds, and the exact source remained unchanged. Selected declarations: 3. Own warnings: strict 0, normal 0. No failed attempts or source repairs occurred.

Final source SHA-256: e1bc970f177de68d3eb6adc13a7e7e5c28b0d38f4decacaa0e336e411c72d9bd.
