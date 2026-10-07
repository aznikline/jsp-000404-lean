# Actual interior-zero partition: checked producer

Status: SCOPED_PASS, 2026-10-07. The final source passed guarded strict
trust-zero checking and a genuine normal module build. All six selected
declarations have exactly the standard axioms `propext`, `Classical.choice`,
and `Quot.sound`. No Git or quota command was run; old frozen sources are
unchanged.

Source: `Jsp000404/ActualInteriorZeroPartition.lean` (678 lines).
Final SHA-256: `58092914604586a5faec35337ef3cdde5afecd6bb914963e6cc86d278ab4dca6`.
The six selected declarations are listed at the end of the source and in
`verification/oct7-actual-interior-zero-partition/selected-names.txt`.

## Real API gap and the chosen route

The existing public APIs provide actual fan order, its sorted direction
map, the map equality with the full direction row, the surrounding-bit
theorem, a window after an actual cyclic gap, and `dirRep` reference shift.
No public theorem was found identifying `rawBit` after reference shift or
identifying a particular flip after cyclic rotation.

Also `PositiveRowFan.exists_shift_window_of_gap` only retains the numeric
gap value. Equal-valued gaps can have different lift-bit behavior, so its
chosen cut cannot simply be asserted to close a `010` bit word.

The new leaf avoids that assertion. It first copies only the necessary
local actual containing-triangle/fan proofs (using the stable public
ordered-surrounding-bit theorem). A pure finite-list lemma selects an
actual adjacent opposite-bit pair from that mixed original fan. Its
actual angle cap proves that its actual adjacent direction gap is at least
`lambda`; local list lemmas put that very gap in the complete actual
`cycGaps` row. No generated private declaration name is referenced.

The existing actual gap-window theorem then gives an internally selected
original reference ray `z`, its false new bit and coordinate zero, and
`0 <= x <= H <= pi-lambda`.

## The cut class may wrap

A fresh actual containing triangle in the new reference supplies a true
ray `m` followed by a false ray `r`. It is chosen from `010` or `101`
according to the first ray's bit; the proof does not force that first bit
to be false.

The scalar classifier uses four projective tags, but three actual classes:

* false with `x <= x_m`: class 0;
* true with `x <= x_r`: class 1;
* false with `x > x_m`: class 2;
* true with `x > x_r`: class 0 again.

Physical coordinates are `x` for a false bit and `x-pi` for a true bit.
Thus class 0 joins the negative tail and initial positive interval across
the actual ray cut. Witnesses `z,m,r` certify all three classes nonempty.

The private scalar proof uses only internally derived facts:
opposite-bit differences are at least `lambda`, `H <= pi-lambda`, and
`H < 4*lambda`. The latter follows from the original LOW lower scale.
The three potential boundary inversions would each put four disjoint
`lambda` steps inside `[0,H]`, contradicting `H < 4*lambda`.

Finite actual class extrema in the physical coordinates supply diameter
endpoints and nonnegative spans. If there is no negative tail, the two
internal flip costs and the closing gap cost give total span at most
`pi-3*lambda`. If the tail is present, the three internal flip costs give
the same bound. Endpoint angles realize the spans; they are not merely
caller-supplied upper bounds. Same-class angles are bounded by their
span, and different-class angles are at least `2*lambda`.

## Actual producer and scope

The public `Data` contains actual original subtype indices, three actual
witnesses, actual diameter endpoints, realized physical spans, their
nonnegativity and total bound, and the actual angular inequalities.
`actual_partition_nonempty` constructs all of this internally, and
`actualPartition` makes the fixed noncomputable choice.

The coarse construction actually works for every original interior LOW
row; its score-zero hypothesis is retained in the requested public
interface. It does not reuse the score-one cut at `2*lambda`, nor claim
the sharper score-one remainder bound for score zero.

The singleton consumer uses the actual different-class angle bound and
`rowGain_pos_of_forall_angle_ge`. It proves positive gain for a singleton
target, regardless of that target's score. Only a separate original
minimum-counter budget forbids such a singleton when the target has
original score zero. No all-target-zero conclusion, hull witness in each
class, hull-nine claim, or F17 exclusion is exported here.

## Actual verification and preserved attempts

| Check | Exit | Seconds | Peak process-tree RSS, KiB |
| --- | ---: | ---: | ---: |
| Strict attempt 1, API/syntax failure | 1 | 63.505 | 5,192,368 |
| Strict attempt 2, final trust-zero | 0 | 80.070 | 4,665,632 |
| Genuine normal module target | 0 | 66.310 | 4,761,728 |

All runs used the same 8 GiB process-tree and 180-second limits. The guard
checked for more than one active Lean process; no resource or concurrency
stop occurred. The normal log confirms the owned module was actually built
and the build completed successfully. Strict and normal both printed all
six selected declarations with standard axioms only.

The first actual attempt exposed list-constructor/parser and Pairwise API
issues, incomplete tactic fallback for the mixed physical-coordinate case,
and a missing explicit `x r <= H` fact for linear arithmetic. They were
repaired only in this new leaf. The finite-extrema total-span argument
required no mathematical change. The exact failed source and raw output
are preserved alongside the exact successful snapshots and outputs.

The final source retains one harmless style warning at the `solve` branch:
`tac1 <;> tac2` can be written with `;`. It is recorded as one own warning in
both checks. Inherited warnings in the normal log are counted separately;
the style warning was not suppressed and no extra compiler round was spent
on changing the checked source.

Before compilation, a duplicated final namespace `end` was removed. The
exact uncompiled 675-line candidate is preserved at
`verification/oct7-actual-interior-zero-partition/source-only-before-end-repair.lean`
with SHA-256 `1b4f81e2588fa22f3109cf4ce131ec686570b31d21345ce7187aa712d445643e`.
That pre-compiler repair is not counted as a failed Lean attempt.

The matching `JSP404_ACTUAL_INTERIOR_ZERO_PARTITION_RECEIPT_20261007.json`
binds source, selected names, every raw output/snapshot, guard runner and
real normal artifacts. The sole compiler window was released to root for
Uniform immediately after normal completion, before document cleanup.
