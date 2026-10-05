# Actual single-positive-row split receipt

Owned new sources: `Jsp000404/SafeFanReference.lean` and
`Jsp000404/SingleSplitScorePreservation.lean`. All previously frozen helpers,
root imports, audit files, and other agents' sources are unchanged. No commit,
full Lake build, or account-quota operation is performed by this lane.

## Safe reference: strict PASS

`exists_safe_reference` uses finite avoidance of nonzero real dual-map
kernels. For a finite nonempty family of nonzero plane vectors, it constructs
a nonzero reference whose Kahler imaginary part is nonzero against every
vector. Consequently every limiting projective coordinate lies strictly
inside `(0,π)`. `exists_safe_continuous_coordinates` constructs the reference
and proves coordinate continuity from actual continuous vector trajectories.
The caller does not supply seam safety or projective continuity.

The clean source passed scoped `lean --trust=0 -o ...` with three audited
exports using only the standard three axioms, no warnings, exit 0 in 2.910 s.
Frozen-candidate SHA:
`400d2815733dc8e6a21b94af332331ac7a1ff8399825173a7089dbd2d6658c08`.
Raw log: `.lake/safe-fan-reference-strict-20261005.log`.
Time maximum RSS: 2,649,587,712 bytes; sampled Lean: 2,602,827,776 bytes;
sampled group: 3,303,669,760 bytes. Actual Lean remained below 3.5 GiB.

## Complete single-split interface written

The final theorem has only the original geometric inputs:

```lean
exists_single_positive_split_preserving_potential
  (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
  (hs : 3 ≤ s) (c : Fin s → Plane₂)
  (hleg : Section4Legality c lam) (v : Fin s)
  (hpos : 0 < rowScore lam (directionRow o e c v))
  (htau0 : 0 < tau) (htau : tau < lam) :
  ∃ lam', tau < lam' ∧ lam' < lam ∧
    ∃ c' : Fin (s+1) → Plane₂, Section4Legality c' lam' ∧
      potential lam' (directionRows o e c') =
        potential lam (directionRows o e c)
```

This is not a theorem for an arbitrary admissible midpoint axis. It internally
extracts a positive genuine gap, chooses the specific end-lambda rotated axis,
and derives its original-ray angular caps. It builds the actual pair points
on exactly `s+1` indices, normalizes sibling rays by removing positive epsilon,
keeps external actual difference trajectories, constructs per-row safe refs,
and proves exact positive-epsilon `directionRow = sortedFan` identities.

The limiting stars are identified internally: every unselected row has its
old star plus the repeated direction towards the cloned center; either clone
has the old star plus the axis. Every outgoing point and every repeated
direction is retained. Proved score-dedup invariance removes only zero-gap
direction multiplicities when comparing scores, never centers or potential
rows. Negative sibling coefficients are handled projectively.

The common-scale analytic theorem and actual legality event meet at the same
positive epsilon. Generic nonzero-vector reference-score invariance permits
the safe continuity refs and the endpoint calculation ref to differ. A
post-gap coordinate zero is used only for static score calculation, never
as the input to a false boundary-coordinate continuity claim.

The endpoint calculation proves that the real wrap is split into `H-lambda`
and `lambda`, including `H=π`. `rowScore_erase_head'` and the frozen end-split
floor identity give merge gain exactly one. A local actual score table then
proves both clone scores are `k_v-1` and all other scores remain their old
values. Finally the actual sigma-child sum uses `2*2^(k_v-1)=2^k_v`.

## Current validation boundary

The latest scoped checks have reached and printed standard-only axioms for
all 26 lower declarations, including actual fan identification, generic ray
reference invariance, both limiting star score identities, safe normalized
coordinate construction, endpoint axis extraction, exact endpoint score
decrement, and the common legal positive-epsilon score event.

The earlier whole-source checks exited 1 only in the final sigma-child
constant sum: the conditional `Fin` cardinality was left as `univ.card`.
Rewriting the inner constant sums before the selected-parent case split
resolved the type issue; no geometric premise or frozen helper was weakened.

The complete source now has a **formal strict PASS**, including the final
actual potential-preservation theorem. After integration released the fourth
heavy slot, `lean --trust=0 -o ...` exited 0 in **3.975 s**, with **27 audited
exports using only standard-three axioms or a subset**, no warnings, and a
real `.olean`. Time maximum RSS: **3,208,642,560 bytes**; sampled Lean peak:
**3,142,287,360 bytes**; group peak: **3,909,238,784 bytes**. Actual Lean stayed
below the authorized 3.5 GiB cap; the group sum was recorded only.

Frozen source SHA-256:
`af04d663329454b62a170646b9af0c27ef8c5a939ff2435a74acfa7c124c0284`.
Both new sources are now frozen. All own compiler processes exited and the
next heavy slot was explicitly released to the N4 scalar/extractor lane.

Raw current log: `.lake/single-split-score-preservation-strict-20261005.log`.
The separate `F-s` strong induction is now being written only in the newly
authorized `ActualPotentialInflation.lean`; it does not alter these frozen
sources. No capacity, ordinary point count bound, or all-`n` closure is assumed
by the single-split theorem or the intended inflation theorem.
