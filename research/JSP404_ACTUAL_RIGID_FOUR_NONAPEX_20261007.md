# Original nonapex witnesses in a rigid-four selection

Status: SCOPED_PASS. The exact source passed strict trust-zero and a
genuine normal target build; the selected declaration uses only
propext, Classical.choice, and Quot.sound.

Source: `Jsp000404/ActualRigidFourNonapex.lean`.
Checked export: `Jsp404.ActualRigidFourNonapex.actual_rigid_four_nonapex`.

The inputs are the original actual n4 LOW Model to cap 16, a nonzero
reference, an injective selection of four original rigid points, and a
selected point i that is an original full-hull nonvertex of original
score one. Rigid profiles are the same as in the checked R4 producer:
original interior score one, or original score two with an actual
original angle at least 2*lambda. There is no potential-18 premise.

The producer internally constructs the original actual three-class
partition P at pick i and obtains the checked actual rigid-four geometry
G. P belongs to the full original configuration at scale lambda. G's
physical windows belong to the selected four-point configuration at
mu=2*lambda. These are distinct scopes and are kept separate throughout.
Neither P, a selected hull/window, nor doubled legality is a caller
input.

First, for any class label k, some selected point other than i must lie
outside k. Otherwise both actual endpoint rays of G's complete window
at i map into class k of P. The original same-class angle bound gives
that window width at most R=pi-4*lambda, contradicting G's actual lower
width bound 2*lambda. This argument concerns the complete physical hull
window; it makes no claim that every selected triangle angle is at
least 2*lambda.

If a selected point j were in original apex class 1, the preceding fact
would supply another selected point k outside class 1. They are distinct
because their original class labels differ. P's genuine apex-angle
bound gives angle(j,i,k)>=3*lambda. G's actual doubled legality gives
that same angle at most pi-2*lambda. The original LOW strip implies
pi<5*lambda, so these inequalities contradict each other. Thus all three
other selected rigid points avoid the original apex.

Use the first fact again with labels 2 and 0. Avoiding class 1 and class
2 forces an actual selected witness in class 0; avoiding class 1 and
class 0 forces one in class 2. They are distinct. The output Data carries
the internally produced original partition, apex exclusion for all three
other selected points, and both actual selected nonapex witnesses.

Independent read-only static review found no specific mathematics or
API blocker. It checked the selected-to-original Subtype embedding,
window endpoint mapping, apex lower and doubled-angle upper bounds,
all point inequalities, and Fin 3 witness extraction. Actual strict checking, the axiom report and genuine normal target
build all succeeded on the unchanged candidate source.

The proof uses only doubled legality's true upper bounds on selected
triangle angles and the complete-window lower bound. It does not infer
an arbitrary-triangle lower angle bound, transfer selected hull status
back to the original hull, or accept a caller class/angle/gain table.
No old READY source or receipt was edited. No Git operation was run;
the completed guarded Lean checks are recorded below.

This completes the shared nonapex step from PAPER E. It does not
close every F18 case, full F17/F18 capacity, or the original arbitrary-N
lower bound.

Verification: strict attempt 1 exited 0 in 37.02 seconds with maximum
RSS 5,810,946,048 bytes; genuine normal attempt 1 exited 0 in 32.31
seconds with maximum RSS 5,743,869,952 bytes and actually built the target
in 9018 jobs. Both 8 GiB / 180 second guards remained clear. Both
own-source warning counts were zero. No failed attempt or source repair
occurred. Raw inherited warnings are preserved and counted separately.

Final source SHA-256: 9527780746c6b7035a89c9f47bb674c956d7327046c9ba83188a83ba2a0d8985.
