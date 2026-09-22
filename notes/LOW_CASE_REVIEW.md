# Semantic review of the saturated low-regime capacity proof

## Verdict

No actionable proof defect was found in the reviewed chain.
`Jsp404.potential_le_two_pow_of_saturated` proves the stated low-regime
capacity bound for every finite size `s ≥ 2`, assuming the original
`Section4Legality` conditions and the existence of a saturated center.
There is no upper bound on `s`, no assumed graph cover or coloring, and
no certificate or global capacity premise.

The source review covered `ConeCorridor`, `AnchoredRows`, `IntervalPacking`,
`BinGraphs`, `ChartInvariance`, and `OneSaturatedLow`, together with the
definitions of legality, defect, score, and potential and the imported
binary-subcube counting argument. An independent read-only check covered
the theorem premises, full-fan weights, and small configurations.

## Exact statement and meaning

The final theorem takes:

- An orientation `o` and an arbitrary nonzero reference vector `e`.
- An injective configuration `c : Fin s → Plane₂`, with `s ≥ 2`.
- Positive `lam`, `n ≥ 2`, and `floor (pi / lam) = n`.
- Every angle of every distinct center triple at most `pi - lam`.
- A vertex `v` whose actual direction row has `rowDefect n lam = 1`.
- The strict low-regime condition `pi / lam - n < 1/2`.

It concludes

```text
sum_i 2 ^ rowScore lam (directionRow o e c i) ≤ 2 ^ n.
```

`Section4Legality` contains exactly positivity, injectivity, and the
triangle angle cap; it contains no combinatorial certificate. The
separate positivity argument in the final theorem repeats its existing
field and does not strengthen the geometric assumptions. Given the
floor identity, the fractional part is automatically nonnegative.

Saturation means defect one. Because each actual nonempty row has at
most `n` lambda-cells, `rowScore_eq_sub_defect` identifies this with the
maximal exponent `n - 1`. The theorem asks for at least one saturated
center; it does not assume exactly one.

## Chain checks

1. **Actual directed rays.** `saturated_ray_window` uses the already
   proved saturation-angle bound and the triangle cap to place the
   outgoing anchor rays in one oriented window. It does not infer a
   directed cone merely from unoriented line proximity. The window
   width is `beta = pi - n * lam`, with `0 ≤ beta < lam/2` in this regime.

2. **Chord corridor.** The two endpoint triangle caps imply that every
   non-anchor chord line lies in `[lam, pi - lam/2]`. The proof handles
   both choices of the directed representative by reversing the chord
   when necessary. All corridor premises are constructed from legality
   and saturation in `OneSaturatedLow`.

3. **Bin geometry.** The number of bins is `m = n - 1 > 0`, and the
   width is `(pi - 3*lam/2)/m`. The floor identity and `n ≥ 2` make this
   width positive. The strict low-regime inequality makes it strictly
   smaller than `lam`. The corridor ends before `pi`, so all cone
   centers stay in the half-plane chart used by the angle calculation.

4. **The full original row.** `directionRow_anchor_cons` proves that the
   complete row at each remaining center is exactly its anchor direction
   followed by the direction row of the remaining subconfiguration.
   It does not replace the complete row score by the deletion score.
   `anchored_rowScore_eq_linear` includes both endpoint gaps, closing at
   `theta i + pi`; the two margins are at most `lam`.

5. **Counting and weights.** The occupied-bin cardinality is proved equal
   to the active graph-coordinate cardinality, including the conversion
   from `Fin m` to natural bin indices. The uniquely assigned bin graphs
   cover every pair. Each is a subgraph of a cone graph of radius
   `width/2`; the strict width bound converts the non-strict original
   angle cap to the strict bound needed for two-colorability. Distinct
   vertices therefore receive disjoint binary subcubes. Their volumes
   are `2^(m - active.card)`, and the actual full-row weight is no larger
   by the local empty-bin bound.

6. **Assembly and transport.** The remaining centers contribute at most
   `2^(n-1)`. The anchor contributes at most `2^(n-1)` by the unconditional
   single-row floor bound. The exact `succAbove` sum decomposition gives
   `2^n`. `ChartInvariance` proves equality of each actual row score and
   hence of the entire potential between any two nonzero reference
   vectors of the same orientation. The final theorem uses that equality
   to return to the original `e`; it has no selected-chart restriction.

## Boundary cases

- **Two centers.** Each full row is a singleton with wrap gap `pi`, score
  `n - 1`, and defect one. Both centers are saturated, and the potential
  is exactly `2^n`. After removing the anchor, the remaining row is empty.
  The bridge correctly uses `linearGapScore lam theta (theta+pi) [] =
  gapScore lam pi`, rather than the zero score of an empty cyclic row.
  The graph cover is vacuous, all coordinates are inactive, and its
  single remaining vertex has cube volume `2^(n-1)`.

- **First strip, `n = 2`.** There is one bin, of width `pi - 3*lam/2`.
  The assumptions imply `2*pi/5 < lam ≤ pi/2`, so the width is positive
  and strictly below `lam`. No division by zero or `n ≥ 3` assumption
  enters the proof.

- **Exact grid endpoints.** `uniformBin` is the floor index clamped at
  `m - 1`. The left endpoint is assigned to bin zero; an internal grid
  boundary is assigned to the bin on its right; the final endpoint is
  assigned to the final bin. Closed geometric containment is therefore
  compatible with unique graph assignment. Strict `width < lam` supplies
  the strict floor inequalities even when a direction lies at an endpoint.

- **Repeated directions and a moving chart cut.** Multiplicities are
  retained in the row identities and removed only when counting occupied
  bins. Reference transport preserves cyclic differences and the special
  full-circle wrap gap of a constant row. Sorting the shifted row is
  proved to be a cyclic cut, including directions exactly at that cut.

- **Phase boundary.** `delta = 0` is included. `delta = 1/2` is excluded;
  there the chosen width becomes `lam`, losing the strict inequality used
  by both the counting and cone-coloring steps. The statement accurately
  reflects this restriction.

## Verification evidence and remaining scope

The existing `verification/one-saturated-low-build.log` records a
successful build and reports only `[propext, Classical.choice, Quot.sound]`
for both assembly exports. The bin and chart build logs give the same
standard-axiom result for their audited exports. Imported modules still
contain unrelated admitted results; those do not occur in the dependency
closure of this final theorem. No new build was required for this
read-only semantic review.

This result closes the saturated low-regime case. It does not prove the
zero-saturation low case, the high regime, or the full theorem for all
legal configurations. It bounds the defined center potential; any final
generalized-configuration point bound still uses the existing bridges
from those point counts to this potential and must discharge its other
cases.

Documentation follow-up: the old “Connections still required” items in
`notes/LOW_CORRIDOR.md` are now fulfilled for this saturated low case,
including arbitrary-reference transport. They should be updated without
claiming that the remaining general-capacity cases have been solved.
