# Actual eight-center R2 rank regions

2026-10-07 UTC: **READY — genuine strict and normal compiler PASS.**
`Jsp000404/ActualN4R2RankRegions.lean` has two checked public exports. Both
use exactly `propext`, `Classical.choice`, and `Quot.sound`, with zero own
warnings. Final strict attempt 2 took 74.576 seconds and the genuine own
Lake target build took 57.810 seconds; neither reached the 8 GiB or 180 s
limit. The first strict attempt failed on inference of the generic cluster
function's final implicit `x,y` arguments. Its actual source snapshot and
raw output are retained. An explicit lambda supplies the expected argument
type in the final source. This scoped proof is not a finite exclusion.

The new actual chart interface takes a genuine `SatChart` on the original
eight points, original anchor defect one, and two distinct original
non-anchor rows of defect two. It internally uses
`SatScalarExtraction.sigma`, its real angle ranking, and the existing
arbitrary-size actual cluster theorem. The result retains the actual common
region together with the two ordered low ranks:

- All five other ranks below the lows: low ranks `(5,6)`.
- All five other ranks between the lows: low ranks `(0,6)`.
- All five other ranks above the lows: low ranks `(0,1)`.

The original-configuration interface constructs the actual saturated ray
window, reference vector, rank permutation, and chart internally. Its input
defects are in the caller's original reference chart; the checked reference
invariance theorem transports them to the internal chart. No caller-supplied
rank array, scalar realization, or tail-defect hypothesis is needed.

## Existing geometric source of the reduction

`FivePointCapacity.lean` contains the genuine arbitrary-size theorem
`two_defect_two_theta_clusters` (line 564), the pure order lemma
`theta_regions_collapse` (line 759), and their original-configuration
consumer `defect_two_pair_theta_cluster` (line 816). The new chart interface
uses the first two so that the conclusion concerns the given actual chart;
they are the same checked geometric ingredients underlying the consumer.
Their hypotheses allow any `s+1` points with `4 <= s`, so `s=7` is within
scope. They do not require a defect-three tail or a six-point configuration.

The strict real rank order makes the three index-pair conclusions elementary
finite order facts. The current Mathlib declaration
`StrictMono.lt_iff_lt` was checked read-only in
`Mathlib/Order/Monotone/Basic.lean`; it reflects the needed real inequalities
back to finite-rank inequalities. The final whole-source checks validated the
Fin7 boundary arithmetic and dependent actual-chart elaboration.

## Consequence for the proposed remaining data route

The shared 24,698-word packet catalog and `exists_catalog_model_word` do not
depend on low-row ranks and can be reused. A **bare**
`M : GenericModel 7 4` does not retain the actual configuration and cannot
automatically use this geometric three-region theorem. An all-scalar theorem
would still need all 21 unordered low pairs, or 12 classes after a separately
proved general reflection. For the actual eight-point route, the three
geometric regions suffice. The current between terminal is scoped to `(0,6)`;
its complete concrete replay still needs its own final validation. A new
same-side `(0,1)` replay and a genuinely proved Fin7 model reflection
could then handle the two outer classes. The present source does not prove
that reflection or the new same-side replay.

No six-point special outer-class conclusion is transferred to eight points.
No arbitrary-pair replay, full actual eight-point exclusion, all R2 capacity,
or original arbitrary-N completion is claimed.
