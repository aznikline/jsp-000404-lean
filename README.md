# JSP-000404: Blumenthal–Sendov angle problem

**Partial formalization. The full arbitrary-N lower bound is not yet
proved, and this revision is not a complete prize submission.**

The project uses actual Mathlib Euclidean-plane points and unoriented
angles. `Jsp404.alphaN` is Sendov's two-band formula; `Jsp404.PtCfg`
contains a list of distinct points.

- `Jsp404.sendov_upper` is proved for every N >= 3: for every epsilon > 0
  there are exactly N distinct points whose angles are all below
  `alphaN N + epsilon`.
- `Jsp404.sendov_lower_le_sixteen` proves the original lower bound for
  every N from 3 through 16. `sendov_alpha_eq_le_sixteen` proves equality
  of the original extremal quantity and formula over the same range.
- The complete n = 1, 2, and 3 capacity strips are proved. At n = 3,
  `N3HighPairClosure.strip_capacity` combines LOW cap 8 and HIGH cap 10
  for every number of actual centers. `strip_certificates` discharges
  both original certificate-existence obligations in this strip.
- `GlobalFiveLowCapacity.potential_le_two_pow_of_le_five_low` proves
  LOW capacity for every n >= 3 and three through five actual centers.
- `SmallConeLowCapacity` proves the sharp LOW bound for every actual
  legal configuration with n >= 3 when the rays at one anchor have physical
  spread below lambda/2. It also excludes saturation at the lower LOW
  boundary for an original counterexample. General NoSAT capacity remains open.
- `N4StrongFourRowGeometry.between_pure_tail_impossible` excludes the
  actual n = 4 six-center between class with a saturated anchor, two
  defect-2 rows, and three defect-3 tail rows. The two outer theta classes
  and the remaining n = 4 cases are open.
- `N5StrongFourRowGeometry.between_pure_tail_impossible` closes the same
  actual six-center pure-tail between class at n = 5 in both bands. Its
  HIGH arithmetic terminal covers all 1024 triangle arms internally.
- `R2N4FiniteReduction` reduces arbitrary-size n = 4 R2 capacity to
  actual configurations through eight centers. Its finite capacity
  premises remain explicit and unproved.
- Five checked foundation modules provide finite gap/fan floor stability,
  exact defect preservation under scalar-model reflection, the specified
  n = 3 scalar terminals, and actual projective-ray continuity helpers.
  The actual inflation theorem below assembles those analytic foundations.
- `ActualPotentialInflation.exists_exact_actual_inflation` constructs
  exactly the original potential's many distinct actual points at a
  parameter strictly between any supplied positive threshold and the old
  parameter. It assumes no capacity bound and does not assert final score
  zero. Sharp ordinary-point bounds in later strips remain open.
- `ActualFlatPotentialInflation.exists_exact_flat_actual_inflation`
  strengthens this to final score zero in every row and final potential
  equal to the original F. It still assumes no capacity bound.
- `ActualProtectedInflation.exists_exact_protected_actual_inflation`
  preserves the positions and scores of any injectively selected p rows,
  the original total potential F, and a strict parameter interval. It
  constructs exactly p + (F - protectedMass) actual points and makes every
  unprotected final row score zero. The empty and fully protected cases
  are included.
- `R2N4PureTailInflation` consumes an actual n = 4 HIGH configuration with
  three distinct protected rows of scores 3,2,2. F = 21 yields exactly
  eight actual points with five zero-score tails; F = 22 yields nine with
  six zero-score tails. These constructions supply no bare point exclusion.
- `SatScalarExtraction` constructs necessary generic scalar models from
  actual saturated charts, preserving delta and every full row defect.
  Seven/eight-center interfaces are included; inverse planar realization
  and capacity are not conclusions.
- `ActualCapacityFromCardinality` consumes an independently proved bare
  actual point exclusion to bound the original potential. Its proved
  nine/eleven-point instances recover capacities 8 and 10 above their
  thresholds; it supplies no new later-strip cardinal bound.
- `ConeDeletionProgress` gives actual deletion progress from an explicit
  common oriented cone at a least-score point. Existence of such a cone
  for arbitrary overfull configurations remains unproved.
- `SixExactFloorKernel.symbolic_between_impossible` excludes the HIGH
  `ModelSix` row-defect profile (2,3,*,3,2) for every natural n >= 4.
  Row 2 is arbitrary. The theorem internally covers all 1024 triangle
  arms, including all 62 surviving directions, without caller mask or
  acyclicity hypotheses. Other profiles and the original arbitrary-N
  capacity theorem remain open.
- `ActualSixBetweenClosure` consumes six actual legal points with a
  saturated anchor, n >= 4 and HIGH. It constructs the ray chart and
  actual angle-rank permutation internally and excludes the ranked profile
  (2,3,*,3,2), with defects measured in the original reference chart.
  The middle rank is unrestricted.
- `N4R2CriticalReifiedRow` and `N4R2CriticalCycleSoundness` provide
  complete-row bridges using actual permutation and sorting fields, plus
  one conditional five-arc sample. The full 24,698-word traversal and
  an independent eight-point exclusion remain unproved.
- `N4R2SharedCycleChecker` proves finite Boolean affine-cycle soundness
  with genuinely interpreted edges. It constructs complete sorted model
  rows and their seven gaps internally, supplies necessary low-row arcs,
  and checks one ascending nine-edge helper. Word decoding and exhaustive
  catalog replay remain open; checker acceptance alone is not a capacity proof.
- `SharpNearestGeometry` proves two actual distance/angle constraints for
  nearest neighbors. Three-run extraction and the critical-model capacity
  conclusions remain open.
- `ActualInteriorOneNearest` selects a genuine containing triangle from
  the original full hull. In n = 4 LOW, an original interior score-one row
  gives an exact score-one selected fan and necessary actual angle bounds.
  A separate four-center theorem gives positive interior-row gain for
  every other-center deletion. General three-run and nearest-neighbor
  exclusions remain open.
- `ActualMinimumDeletionNormalForm` proves an exact local deletion ledger
  under an explicit least-score/divisible-cap normal form.
  `ClosestPairTriangleExclusion` gives empty triangles based on an actual
  closest pair when lambda > pi/6. Neither supplies a general merge step.
- Original LOW/HIGH counterexamples now yield an actual attained flat
  cardinality maximum in the same band, bounded independently by the
  classical coarse power. Every deletion has gain at most one per survivor
  and at most one positive incoming emitter. Excluding those constrained
  counter-models geometrically remains open.
- An actual least-cardinality realization of the attained band maximum
  now gives strict deletion below that maximum and an acyclic gain graph.
  A closest-pair zero-gain direction has an actual outward witness
  when lambda<=pi/4.
  Score plateaux preserve row/gap scores strictly above the lower band
  boundary; no sharp point bound or boundary Flat claim follows.
- Minimum actual counter-cardinality now derives deletion potential at most
  the specified cap. Maximizing at that fixed cardinality preserves the
  weighted model and interior score plateau. A center outside the
  full-hull vertex set has original row defect at least three; defect at
  most two implies a vertex of the full original hull.
- `Jsp404.sendov_lower` is the unresolved arbitrary-N lower target and
  still depends on `sorryAx` in its N >= 17 branch.
- `Jsp404.sendov_alpha_eq_of_selection` connects a future general
  capacity theorem to equality with the genuine geometric extremal
  quantity. Its `GadgetSelection` argument remains unproved. The direct
  geometric route is now assembled in `sendov_alpha_eq_of_geometricCertificates`;
  its general certificate existence premise also remains unproved.

The eleven-point bundle is described in
[`research/JSP404_ELEVEN_INTEGRATION_PROGRESS_20261005.md`](research/JSP404_ELEVEN_INTEGRATION_PROGRESS_20261005.md).
The subsequent local n = 4 result is described in
[`research/JSP404_N4_INTEGRATION_PROGRESS_20261005.md`](research/JSP404_N4_INTEGRATION_PROGRESS_20261005.md).
The latest foundation and diagnostic bundle is described in
[`research/JSP404_FOUNDATIONS_PROGRESS_20261005.md`](research/JSP404_FOUNDATIONS_PROGRESS_20261005.md).
The n = 5 local certificate and additional finite foundations are described in
[`research/JSP404_N5_INTEGRATION_PROGRESS_20261005.md`](research/JSP404_N5_INTEGRATION_PROGRESS_20261005.md).
The latest actual inflation and generic extraction bundle is described in
[`research/JSP404_INFLATION_PROGRESS_20261006.md`](research/JSP404_INFLATION_PROGRESS_20261006.md).
The subsequent capacity transport and fixed-direction symbolic result are in
[`research/JSP404_TRANSPORT_PROGRESS_20261006.md`](research/JSP404_TRANSPORT_PROGRESS_20261006.md).
The latest flat inflation and local geometry results are in
[`research/JSP404_FLAT_GEOMETRY_PROGRESS_20261006.md`](research/JSP404_FLAT_GEOMETRY_PROGRESS_20261006.md).
The latest maximum-band and fixed-mask extensions are in
[`research/JSP404_MAXIMUM_BAND_PROGRESS_20261006.md`](research/JSP404_MAXIMUM_BAND_PROGRESS_20261006.md).
The minimum-cardinality, closest-pair and fixed-direction extensions are in
[`research/JSP404_MINIMUM_CARD_PROGRESS_20261006.md`](research/JSP404_MINIMUM_CARD_PROGRESS_20261006.md).
The minimum-counter and full-hull extensions are in
[`research/JSP404_MINIMAL_COUNTER_GEOMETRY_PROGRESS_20261006.md`](research/JSP404_MINIMAL_COUNTER_GEOMETRY_PROGRESS_20261006.md).
The uniform between-profile and protected actual inflation publication is in
[`research/JSP404_SYMBOLIC_BETWEEN_PROTECTED_PROGRESS_20261006.md`](research/JSP404_SYMBOLIC_BETWEEN_PROTECTED_PROGRESS_20261006.md).
The subsequent actual profile, interior-fan and shared-cycle foundations are in
[`research/JSP404_ACTUAL_LOCAL_FOUNDATIONS_PROGRESS_20261007.md`](research/JSP404_ACTUAL_LOCAL_FOUNDATIONS_PROGRESS_20261007.md).
The proof boundary and branch audit are in [`notes/STATUS.md`](notes/STATUS.md).
Conditional results with standard
axioms are not presented as proofs of their extra hypotheses.

## Build and inspect

Lean: `leanprover/lean4:v4.34.0`.
Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
Transitive dependencies are pinned in `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean --trust=0 -M8000 -j1 verification/oct5-review/ProofAudit.lean > verification/oct7-foundations-review/oct7-foundations-composed-audit.txt
python3 tools/check_proof_axioms_20261005.py --log verification/oct7-foundations-review/oct7-foundations-composed-audit.txt
```

`lake build` succeeds with the documented unfinished declarations.
The audit explicitly exposes the unresolved lower root; a successful
build alone is not a completion certificate. Latest checked output is
in [`verification/oct7-foundations-review/oct7-foundations-composed-audit.txt`](verification/oct7-foundations-review/oct7-foundations-composed-audit.txt).
The same gate with `--mode root` intentionally rejects the unresolved
arbitrary-N lower theorem. Its rejection is retained as a negative control.

## Sources and attribution

The mathematical result is due to Sendov, building on Szekeres and
Erdős–Szekeres. The formula follows the final theorem, with numerator
2 in the intermediate band:

- Sendov, *Minimax of the angles in a plane configuration of points*,
  Acta Math. Hungar. 69 (1995), 27–46, Theorem 4.1, p. 42
  ([journal volume](https://real-j.mtak.hu/7467/)).
- Sendov, *Compulsory configurations of points in the plane*,
  Fundam. Prikl. Mat. 1:2 (1995), 491–516, Theorem 4.4, p. 514
  ([paper record](https://www.mathnet.ru/eng/fpm81)).

The upper construction library is reused, with its original license and
credit to **superpilot69 and ChatGPT 6 Astra**, from a pinned public
revision. See [`ThirdParty/Sendov/README.md`](ThirdParty/Sendov/README.md)
for provenance and hashes. Local contributions connect these constructions
to this project's formula and configuration type and develop the lower
bound infrastructure. Git history and the integration audit retain the
contributions of the existing proof lanes. No new discovery of the
historical formula or exclusive authorship is claimed.
