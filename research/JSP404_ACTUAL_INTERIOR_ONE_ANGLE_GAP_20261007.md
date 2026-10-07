# Actual interior-one angle gap

**SCOPED PASS: two actual geometric exports.** Source:
`Jsp000404/ActualInteriorOneAngleGap.lean`, SHA-256
`f0b2c120fe28be5eed2f19b04d97f86d90cbd2242c3055e77bbad59a1adef39c`.
The first strict `--trust=0 -M8192` check and genuine targeted normal Lake
build both exited 0, with zero new-source warnings and only `propext`,
`Classical.choice`, `Quot.sound` on both exports. There were no failed runs.

Strict checking took 85.36s with maximum RSS 3,598,319,616 bytes. Genuine
normal building took 82.33s with maximum RSS 3,994,255,360 bytes, reported
the actual module as built, and created its real olean, ilean, trace and
hash artifacts. Source, exact strict source snapshot, raw stdout and
artifact hashes are bound by
`JSP404_ACTUAL_INTERIOR_ONE_ANGLE_GAP_RECEIPT_20261007.json` and preserved
under `verification/oct7-actual-interior-one-angle-gap/`.

The two checked exports strengthen the checked general-cardinality
actual window proof from `ActualInteriorOneRuns.lean`:

    original angle < 2*lam  ==>  original angle <= pi-4*lam;
    original angle <= pi-4*lam  OR  2*lam <= original angle.

Their premises are only the original actual legal configuration, nonzero
reference, `lam>2*pi/9`, the original full-hull nonvertex, original row
score one, and the two actual ray endpoints. No angular array, cluster
assignment, flip-count premise or nearest-neighbor conclusion is supplied.

The necessary actual window and finite-ray producers are copied locally
from frozen source SHA-256
`c8cf8f2bf189bc2c28506567f5518a24d7ad6b39f69b19a1992fd487945386db`.
They do not refer to generated `_private` names or change the old checked
source. Actual lift alternation invokes the stable public
`ActualInteriorOneRuns.actual_ordered_surrounding_bits` theorem. The odd
flip/count proofs and nearest-neighbor consumers are not repeated.

The scalar change is precise: false-bit rays on opposite sides of the
actual middle true-bit ray differ by at least `2*lam`, while opposite
lift bits have actual angle at least `3*lam`. Thus an angle strictly
below `2*lam` is in a single narrow class and still has the bound
`H-2*lam<=pi-4*lam`. The equality boundary belongs to the large-angle
branch. The two-export source is 378 lines.

The exact names are:

* `Jsp404.ActualInteriorOneAngleGap.actual_interior_one_angle_lt_twice_le_remainder`;
* `Jsp404.ActualInteriorOneAngleGap.actual_interior_one_angle_gap`.

This is an actual angular rigidity condition needed by the paper mixed-hull
arguments. It does not itself prove a singleton-deletion equivalence,
hull nearest-neighbor capacity, any new F17/F18 exclusion, or the original
arbitrary-N lower bound.
