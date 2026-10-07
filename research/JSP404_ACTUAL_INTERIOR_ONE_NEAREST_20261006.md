# Actual interior-one fan: checked producer scope

Owner: sharp_geometry_oct6b. Started: 2026-10-06. Final checks: 2026-10-07.

**SCOPED PASS: four actual support exports only.** The final source
`Jsp000404/ActualInteriorOneNearest.lean` passed single-file
`--trust=0 -M8192` and genuine `lake build Jsp000404.ActualInteriorOneNearest`,
both exit 0. The four exports depend only on `propext`, `Classical.choice`,
`Quot.sound`; the new source has no warnings. Strict checking took 19.85s
with maximum RSS 3,080,814,592 bytes; normal building took 10.78s with
maximum RSS 3,136,110,592 bytes. The normal build reported the actual
module as built and created its real olean, ilean, trace and hash files.

The initial strict run also exited 0 but had one deprecated `push_neg`
warning. Its log is retained as
`.lake/actual-interior-one-nearest-attempt1-20261006.log`; it is not bound
to the final strengthened source. The final strict and normal logs are
`.lake/actual-interior-one-nearest-strict-final-20261007.log` and
`.lake/actual-interior-one-nearest-normal-final-20261007.log`.
Exact raw stdout copies, selected names and source/artifact/log SHA-256
bindings are in `verification/oct7-actual-interior-one-nearest/` and
`JSP404_ACTUAL_INTERIOR_ONE_NEAREST_RECEIPT_20261007.json`.

The source proves four actual statements:

1. `actual_nested_angles_ge_twice`: actual strict nested betweenness and
   the original legality cap give all three surrounding ray angles at
   least `2*lam`, using their genuine sum `2*pi`.
2. `actual_nested_selected_score_one`: in the original n4 LOW band,
   original full-row score one forces the selected nested three-ray
   row's score to be exactly one. At least one of its actual surrounding
   angles is at most `pi-2*lam`. The original score is preserved here
   by the combination of actual row restriction and the independently
   bounded nested fan, not by an assumed subset score certificate.
3. `exists_actual_interior_one_fan`: from the original full-hull
   nonvertex and original full-row score one, the proof internally
   selects three distinct actual other centers and their strict nested
   witness. It supplies the exact selected score and necessary actual
   angles: all three are at least `2*lam`, and after choosing the one
   at most `pi-2*lam`, each of the other two is at least `3*lam`.
   It uses actual finite-point separation, Caratheodory, legal
   noncollinearity, and the previous two statements.
4. `actual_four_center_interior_emits`: for an original legal four-center
   configuration, the proof internally identifies all three other
   centers with the actual containing triangle. Every deletion of an
   other center has genuine positive gain in the original interior row.
   This is the singleton base case; it neither accepts a supplied gap
   model nor confuses selected-row gain with full-row gain. This theorem
   does not require n4 or a score-one hypothesis.

There is no supplied theta array or capacity field. These are producers
from actual original geometry. No root, frozen proof source, or other
agent's file was edited.

The file deliberately does **not** prove the general interior-one nearest
exclusion. For arbitrary cardinality, the original row's additional rays
still need a genuine twisted three-run extraction with actual lifted
signs, followed by the exact singleton/zero-gain identification. The
four-center theorem does not supply that arbitrary-cardinality bridge.
Consequently the F18 nearest-neighbor budget and its paper subdomain
exclusions in `JSP404_SHARP_GEOMETRY_OCT6B.md` remain unformalized, and
F17, the remaining n4 LOW cases, and the arbitrary-N original lower bound
remain open.

The next precise actual producer is: in `2*pi/9<lam<=pi/4`, from original
`Section4Legality c lam`, original full-hull nonvertex `p`, original
`rowScore ... p=1`, and original actual `rowGain ... (deleteIndex ... q p)=0`,
produce an actual index `j!=p,q` with `angle(q,p,j)<lam/2`. The newly
checked fan can anchor a proof that adding any remaining original rays
does not change selected score one; that equality must then be used to
derive the full actual runs. This producer is not asserted as a Lean
theorem in the present source. Once proved, the already checked
`SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle`
immediately supplies `dist(q,j)<dist(q,p)`. The actual minimum-counter
deletion budget can then discharge the zero-gain premise for light
targets. No caller should supply the three-run or nearest conclusion
instead of this missing producer.
