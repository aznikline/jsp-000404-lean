# Actual rigid-four restriction geometry

Status: SCOPED_PASS. The final source passed strict trust-zero and a
genuine normal target build. Its selected declaration uses only
propext, Classical.choice, and Quot.sound.

Source: `Jsp000404/ActualRigidFourGeometry.lean`.
Checked export: `Jsp404.ActualRigidFourGeometry.actual_rigid_four_geometry`.

The input is the original actual n4 LOW minimum-counter Model to cap 16,
a nonzero reference, an injective selection of four original points,
and their original rigid profiles. Each selected point is either an
original full-hull nonvertex of original score one, or has original
score two with a genuine original pair of distinct noncentral rays
making angle at least 2*lambda. No potential-18 premise is required.

All subsequent facts are produced internally. The actual interior-one
and nonacute-heavy producers give the physical angle dichotomy on every
triangle of the selected points. Actual restriction preserves legality
at lambda. The checked scale-doubling theorem then gives actual legality
of the selected four-point configuration at mu=2*lambda.

The original LOW bounds internally give floor(pi/mu)=2 and
pi/mu-2<1/2. The checked SecondStrip weighted potential theorem bounds
this actual selected potential by four. Four actual weights each at
least one force equality and every mu-score to be zero. This step uses
the weighted potential theorem, not merely a cardinality bound.

Selected full-hull membership is derived anew for the selected actual
configuration: its actual mu-row cells are at most two, hence each
actual defect is at most two, and FullHullInteriorDefect rules out a
selected nonvertex. No subset-hull fact is transferred back to the
original full hull, and no original interior label is asserted to remain
interior in the subset.

The producer internally chooses an actual full selected-hull Window at
each selected point. Its two actual endpoint rays have the original
rigid dichotomy. If its width were at most R=pi-4*lambda, its actual
external gap would be at least 4*lambda=2*mu. The checked actual-window
score lower bound with k=2 would force a positive mu-score, contrary
to the internally proved zero score. Therefore each complete selected
hull window has width at least 2*lambda. Its existing legality field
also bounds that width by pi-2*lambda.

The output Data contains the actual doubled legality, floor, exact
potential four, all zero doubled scores, selected hull membership,
and internally selected physical windows with the lower width bound.
These are output conclusions. No caller supplies doubled scores,
selected hull membership, windows or desired angle/capacity conclusions.

Scope correction: the lower angle bound applies to the complete hull
cone at each vertex of the selected quadrilateral, not to every angle
of every triangle. A thin rectangle illustrates why the latter inference
is invalid: for points (+/-100,+/-1), lambda=42 degrees, the full hull
angles are 90 degrees while some triangle angles are about 0.573 degrees.
At mu=84 degrees, all four scores are zero. This is a numerical geometric
diagnostic, not a Lean result or an over-capacity Model counterexample;
its original potential is 16. It is not used by the proof.

Final checks validated the finite-sum equality API, ratio/floor
calculation, chosen-window endpoint dichotomy and k=2 score bound. The
first strict attempt hit the default 200000-heartbeat limit in the last
width conversion. Restricting that arithmetic proof to its actual hsmall
hypothesis resolved it without increasing the global heartbeat budget.
The failed exact source and raw output are preserved separately; their
placeholder axiom output is not a PASS. No admissions, external accepting
tables, intermediate criticality or inherited flatness are used. No old
READY source or receipt was edited.

This supplies the R4 geometry prerequisite from PAPER E. It does not
close all F18 cases, full F17/F18 capacity, or the arbitrary-N original
lower bound.

Verification: final strict attempt 2 exited 0 in 21.48 seconds with
maximum RSS 5,868,240,896 bytes. Genuine normal attempt 1 exited 0 in
19.35 seconds with maximum RSS 5,982,158,848 bytes and actually built
the target in 9016 jobs. Both guarded runs stayed below 8 GiB and
180 seconds. Own-source warnings were zero; inherited normal warnings
are counted separately in the receipt.

Final source SHA-256: 22f9d9a87b7e86ba0c4dfa6a5422aa90f4bf586825ecd7992bade2a347d85623.
