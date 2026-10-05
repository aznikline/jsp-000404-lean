# JSP-000404 — consolidated status

Updated 2026-10-06 after the flat inflation and local geometry audit. **PARTIAL COVERAGE.**
The full arbitrary-N theorem and the prize submission are not complete.

## Current proof boundary

| Obligation | Status | Evidence |
|---|---|---|
| Every N >= 3: sharp upper construction, both bands | PROVED | `UpperBound.sendov_upper`; every epsilon > 0, exactly N distinct points |
| Genuine extremal quantity <= formula | PROVED | `UpperBound.alpha_le_alphaN` |
| Every N from 3 through 16: lower bounds | PROVED | `sendov_lower_le_sixteen`, original `PtCfg` and `alphaN` |
| Every N from 3 through 16: genuine extremal equality | PROVED | `sendov_alpha_eq_le_sixteen`, original `JSP404.alpha` |
| First-strip low/high capacities (n = 1) | PROVED | `SmallStrip.first_strip_capacity_low/high` |
| Second-strip LOW capacity (n = 2), every profile | PROVED | `SecondStrip.potential_le_four_of_second_strip_low` |
| Second-strip HIGH capacity (n = 2), every profile | PROVED | `SecondStripHigh.potential_le_five_of_second_strip` |
| Third-strip LOW/HIGH capacity (n = 3), every actual size/profile | PROVED | `N3HighPairClosure.strip_capacity`, LOW cap 8 and HIGH cap 10 |
| Both original third-strip certificate obligations | PROVED | `N3HighPairClosure.strip_certificates`; actual over-capacity domains are empty |
| Every n >= 3, LOW, three through five actual centers | PROVED | `GlobalFiveLowCapacity.potential_le_two_pow_of_le_five_low` |
| n = 4 six-center R2 between class, pure defect-3 tail | PROVED | `N4StrongFourRowGeometry.between_pure_tail_impossible`; actual saturated anchor and two defect-2 rows |
| n = 4 pure-tail profile reduces to the two outer theta classes | PROVED | `N4StrongFourRowGeometry.six_centre_n4_pure_tail_outer_class`; no model or solver-success premise |
| Full n = 4 capacity and remaining outer/mixed-tail cases | OPEN | The local between exclusion does not supply these cases |
| n = 5 HIGH necessary four-row scalar domain | PROVED | `SixExactFloorKernel.n5_between_impossible`; all 1024 triangle arms, no mask/acyclic premise |
| n = 5 actual six-center pure-tail between branch | PROVED | `N5StrongFourRowGeometry.between_pure_tail_impossible`; LOW actual potential 44 exceeds cap 32 |
| n = 5 actual pure-tail profile reduces to two outer theta classes | PROVED | `N5StrongFourRowGeometry.six_centre_n5_pure_tail_outer_class`; outer classes remain open |
| Uniform parameter across a finite family of continuous fans | PROVED | `UniformFanScoreStability`; explicit continuous safe-chart coordinate families |
| Two common Boolean coordinates, finite weighted packing | PROVED | `TwoCoordinatePacking`; remaining-bit separation is an explicit input, not yet an actual geometric construction |
| n = 4 minimal tail weight profiles and at-most-five overfull subset | PROVED | `R2CriticalWeightClassification`; finite arithmetic, no geometric capacity assumed |
| Arbitrary-size n = 4 R2 reduced to actual capacity through eight centers | CONDITIONAL | `R2N4FiniteReduction`; finite `hcap8`/`hfinite` premises remain unproved |
| Finite nonnegative gap floor margins and continuous finite fan score stability | PROVED | `GapSplitFloorStability`, `FiniteFanScoreStability`; continuous coordinates and strict `(0,pi)` limiting chart are explicit |
| Necessary scalar reflection preserves all five non-anchor row defects | PROVED | `SixModelReflection`; full gaps, endpoints, zero gaps and multiplicity retained |
| Specified scalar n = 3 terminal ranks | PROVED | `N3SixModelTerminal`: rank 1, rank 3, and simultaneous endpoint defects 2; not all rank placements |
| Actual projective-ray continuity and legality/floor-event helpers | PROVED | `ActualScorePreservingExpansion`; supplied finite pert family is not yet identified with all actual rows |
| Exact actual inflation to the original potential's point count | PROVED | `ActualPotentialInflation.exists_exact_actual_inflation`; threshold < final parameter < old parameter, actual legality/injectivity, no capacity premise or final-score-zero claim |
| Exact actual flat inflation, original F point count and potential | PROVED | `ActualFlatPotentialInflation`; every final row score is zero, strict scale interval retained, no capacity assumed |
| Fixed actual minimum-score deletion normal form | PROVED LOCAL BRIDGE | Explicit cap/divisibility, original over-cap and deleted-under-cap hypotheses give exact excess and zero gains |
| Closest-pair-based triangles empty above lambda > pi/6 | PROVED LOCAL GEOMETRY | `ClosestPairTriangleExclusion`; no fourth center inside any such triangle, no adjacency/merge/bare17 conclusion |
| n=4 full-floor arithmetic and small model branch helpers | PROVED PRIMITIVES ONLY | `N4R2CriticalKernelPrimitives`; the actual eight-point exclusion remains open |
| Actual single-positive-row split with exact potential preservation | PROVED | `SingleSplitScorePreservation`; fresh end axis, safe references, positive epsilon and full actual score table |
| Generic saturated scalar extraction, including seven/eight actual centers | PROVED | `SatScalarModel`/`SatScalarExtraction`; internal sigma, exact delta and full non-anchor row defects; necessary direction only |
| Uniform sharp ordinary-point bounds in later strips | OPEN | Actual inflation reduces capacity to an independently required point-count result; it does not prove that bound |
| Bare actual finite exclusion implies original potential capacity | PROVED CONDITIONAL BRIDGE | `ActualCapacityFromCardinality.potential_le_of_bare_exclusion`; independent bare exclusion remains explicit |
| Floor-free actual threshold capacities 8/10 | PROVED | Existing independent bare nine/eleven exclusions consumed through actual inflation |
| Actual common-cone emitter and least-score deletion progress | PROVED LOCAL BRIDGE | `ConeDeletionProgress`; common oriented cone is an explicit local input |
| All natural n >= 4 HIGH four-row ascending scalar mask0 | PROVED FIXED DIRECTION | `symbolic_mask0_probe`; ten explicit ASC triangle hypotheses, not all 62 masks |
| Arbitrary overfull common-cone existence and full direction coverage | OPEN | New local deletion and fixed-mask results do not establish these premises |
| Exact-floor search in natural strips 4..24, 2604 cases | DIAGNOSTIC ONLY | `JSP404_SIX_EXACT_FLOORS_ROUTE_20261005.json`; no completed finite Lean kernel certificate |
| Arbitrary-size LOW capacity when a saturated center exists | PROVED | `OneSaturatedLow.potential_le_two_pow_of_saturated`; no certificate premise |
| Arbitrary-size HIGH capacity when two saturated centers exist | PROVED | `TwoSaturatedHigh.potential_le_high_of_two_saturated`; any original anchors/chart |
| Two saturated centers, at least four centers: every other defect >= 3 | PROVED | `TwoSaturatedDeficit.rowDefect_ge_three_of_two_saturated`; actual original rows |
| Full-row restriction to selected rays / local three-term bounds | PROVED | `TriangleRestriction`; these do not imply the global sum bound |
| Geometric saturation count and half-strip threshold | PROVED | `SaturationPacking`, geometric saturation lemmas in `Induction` |
| Signed-cell normalization at arbitrary size | PROVED | `ProperGaps.ModeA.normalize`, `exists_nonnegative_model` |
| Full classification given geometric certificates | CONDITIONAL | `CertificateIntegration.sendov_alpha_eq_of_geometricCertificates` |
| Arbitrary-N lower bound given the capacity theorem | CONDITIONAL | `Integration.sendov_lower_of_selection` |
| Equality of genuine extremal quantity and formula given capacity | CONDITIONAL | `Integration.sendov_alpha_eq_of_selection` |
| N >= 17 lower bound with no extra hypothesis | OPEN | `MainTheorem.sendov_lower` still depends on `sorryAx` in this remaining branch |
| Final complete-proof submission | NOT READY | Requires the unconditional lower bound and completion audit |

Sharpness means arbitrarily close actual configurations, not an assumed
exact minimizing configuration. `Statement.lean` contains the formula and
point-configuration definitions. The upper constructions are attributed
imports from superpilot69's pinned MIT-licensed development, connected by
new local proofs; see `ThirdParty/Sendov/README.md`.

The 2026-10-05 eleven-point bundle passed all 626 producer source/kernel
checks, all 626 normal Lake targets, four actual consumer source checks,
the 9957-job full build, and the composed 34-declaration standard-axiom
gate. The two-root completion gate correctly rejects `sendov_lower` for
`sorryAx`. Frozen hashes and commands are recorded in
`research/JSP404_ELEVEN_INTEGRATION_RECEIPT_20261005.json`.

The subsequent n=4 local bundle passed five single normal Lake targets,
the actual geometry source trust=0 check, the 9961-job full build, and the
cumulative 48-declaration standard-axiom gate. The original two-root
completion gate still rejects `sorryAx`. Its precise geometric premises
and source hashes are recorded in
`research/JSP404_N4_INTEGRATION_RECEIPT_20261005.json` and
`research/JSP404_N4_GEOMETRY_SCOPE_20261005.md`.

The third foundation bundle passed five sequential genuine normal Lake
targets and the 9966-job full build. Its 28 new audited declarations raise
the accepted standard-axiom set to 76; the original two-root completion
gate still rejects `sorryAx`. Producer strict source results are retained
without rerunning frozen proofs. The precise source, log, diagnostic and
provenance hashes are in
`research/JSP404_FOUNDATIONS_RECEIPT_20261005.json`.

The fourth bundle preserves the n=5 producer's 65 strict and 65 genuine
normal target receipts, then verifies four additional foundation targets
and the new actual n=5 geometry source/target. The full build passes 10035
jobs, and the cumulative standard-axiom gate accepts 95 declarations.
The original two-root gate still rejects `sorryAx`; full n=5 and all N>=17
remain open. The subsequent actual inflation publication is recorded below.
Frozen evidence and exact scope are
in `research/JSP404_N5_INTEGRATION_RECEIPT_20261005.json`.

The fifth publication verifies all five new normal module targets, the
10040-job full build, and a cumulative 142-declaration standard-axiom
gate. The original two-root negative control still rejects `sorryAx`.
The exact actual inflation conclusion does not assert final score zero;
the induction's terminal parameter is freely weakened. Frozen sources,
unaltered producer stdout and precise limitations are recorded in
`research/JSP404_INFLATION_RECEIPT_20261006.json`.

The sixth publication preserves 40 strict symbolic-mask sources and all
40 genuine normal targets. Two new public transport/deletion modules have
genuine normal Lake targets, followed by the 10082-job full build and a
155-declaration standard-axiom gate. The original two-root negative control
still rejects `sorryAx`. Full n=4/n=5 and the arbitrary-N lower target remain
open. Exact premises and frozen hashes are recorded in
`research/JSP404_TRANSPORT_RECEIPT_20261006.json`.

The seventh publication reuses the successful flat-inflation and n=4
primitive normal targets, verifies actual-minimum-deletion and closest-pair
normal targets, and passes the 10086-job full build. Its 24 new public
exports raise the standard-axiom gate to 179. The original two-root gate
still rejects `sorryAx`. Exact frozen scope and producer logs are in
`research/JSP404_FLAT_GEOMETRY_RECEIPT_20261006.json`.

## Integrated material

- Initial user-designated trunk, a historical 2026-09-22 snapshot:
  `lane/integration` at
  `edef86b0d216e7e535a81802d9d43ee6a60b8478`.
- Owner branch `b436a89e72bda007d970f230f95806ed61eacec6`:
  `SaturatedStructure.lean` B1 -> L2-min -> full L2 -> L3,
  plus strict-checker/cross-map material.
- Kernelized geometry from angle-certificate branch
  `d66a6ab9cbe324d3353dbe7300880fb438838589`, followed by
  `0b525bee0ab85f30028a7b76de31356d2ac394e4`: three-center base,
  geometry/deletion bridges, induction, Kraft equivalence and actual
  geometric saturation / half-strip lemmas.
- Wave-1/2 gadget semantics, signed caps, residual arithmetic, ghost
  counterexample, four-center high machinery and alignment invariant.
- `KraftResidual.lean`, copied unchanged from remote commit
  `000e0c50a1adebb0d4ead6e623dae5a2d01cbd4b`: defect-histogram and
  first-overfull-level arithmetic. This is an equivalent algebraic
  formulation of capacity; it does not prove that actual legal
  configurations have nonnegative residuals. The preceding remote
  `KraftPacking` case bundle adds open premises and is not imported as
  a solution to the geometric cases.

At the historical 2026-09-22 remote check, `lane/l1-lowp` and
`lane/v1-vacuum` pointed at their base
`278c44c6e3c45df93de966402d76eb219d139291`. That statement is not the
current remote snapshot. A 2026-10-05 remote check finds:

- `lane/l1-lowp`: `2e19fd3f57ab1b7e9acf00e92e763f16f54db060`.
- `lane/v1-vacuum`: `1e35549f46fee53a28384400aea52813d05f1e94`.
- `lane/integration`: `2917368e2a8fec5456303047ae30a5376473bbb4`.
- AIR: `8f775228238a7efd3ee430a05ea92102f344c64a`.

These are remote-reference snapshots. Proof coverage comes from the typed
source and axiom audits above; it is not inferred from a branch name or an
old RUNNING label.

## Remaining global routes

1. **Gadget route:** arbitrary-size low and high consequences for faithful
   skeletons, followed by the geometry-to-skeleton adapter. `ProperGaps`
   now proves that strict remainders force nonnegative cells, and closed
   remainders can be normalized without changing angles or weight. This
   closes the signed-cell obstruction for capacity transfer; it does not
   assert transport of gadget witnesses or supply the geometry adapter.
2. **Geometric route:** prove the arbitrary-size `CertExists` progress
   lemma or the equivalent Kraft packing bound. Both n = 1 and n = 2
   boundaries and final wiring are proved: `GeometricCertificates`, now
   quantified only over n>=3, implies the full extremal equality.
   This remaining premise itself is OPEN.

The s = 4 high reduction is proved conditional on `AllBadStrip`; it does
not settle arbitrary s. Finite enumerations do not prove the general
vacuum statement. Saturated-point lemmas constrain some profiles but do
not yet bound the total mass in every profile.

Further proof details: `FIRST_STRIP_AND_CELLS.md`, `KRAFT_CRUX_AUDIT.md`,
and `LOW_CORRIDOR.md`. The competitor update at `fc6047f` was read and
qualified against its original archive; its three-term constraints do not
close the global packing step.
`KRAFT_CRUX_AUDIT.md` rejects the incorrect zero-saturation shortcut.
`LOW_CORRIDOR.md` records the completed one-saturated LOW case: actual
row identification, unique direction-bin graphs, coloring, weighted
counting and reference-chart invariance are all proved. The remaining
geometric packing cases, all with n>=3, are LOW with no saturated center
and HIGH with zero or one saturated center. The entire n=2 boundary is
proved by the varying fan-bisector inequality `W*lambda <= 2*pi`.
`TwoSaturatedHigh` closes the complete
two-saturated HIGH case: its remaining normalized mass is <=1/4,
including the three-center boundary through the established base case.
`TWO_SATURATED_RESEARCH.md` records the local HIGH progress and its
completed global corridor/counting assembly.

`FIVE_POINT_ROUTE.md` records the independent fan-bisector argument that
now proves the original theorem exactly for 3<=N<=8. For rejected global
shortcuts and reproducible evidence, see `GLOBAL_PACKING_RESEARCH.md`,
`NO_SATURATION_LOW_RESEARCH.md`, `ONE_SATURATED_HIGH_RESEARCH.md`,
`AVERAGED_BIN_PACKING.md`, and `ONE_SATURATED_HIGH_GEOMETRY.md`.
Experimental success of an adaptive partition is not a proof that one
exists for every configuration.

## Corrected and falsified interfaces

- `maxGap_boundary_emission` (`GeometricDeletion.lean`) is false as
  stated. Checked countermodels: `s = 2` unconditionally, `s = 3`
  conditionally at `lam > pi/2`, and `s = 4` on the square at
  `lam = 5 pi/12` (low regime, all row gains zero;
  `MaxGapCountermodel2.maxGap_boundary_emission_countermodel_s4`,
  standard axioms only). Restricting the quantifier to `4 <= s` is
  NOT a repair — the square is legal at `s = 4`. The square is flat
  with `potential = 4 = sendovCap 2 false`, so it does not refute the
  strict over-capacity consumer domain used by `CertExists` — provided
  `n`/`big` carry the consumer bindings `Nat.floor (pi/lam) = n` and
  `big = false → pi/lam - n < 1/2`; with free `n`/`big` the square
  refutes even that domain (`n = 1`). See `notes/MAXGAP_SPEC_AUDIT.md`.
- The research shortcut "no saturated centers implies K <= 1 in both
  regimes" is false. `PentagonPacking.strict_no_saturation_counterexample`
  proves a proper, nonnegative strict model with K = 5/4 and no saturation.
  The target high cap K <= 5/4 is not contradicted. Numerical nine-point
  evidence also rules out repairing the shortcut by excluding flat cases.
- Loose selection without `Proper`: ghost-vertex counterexample.
- Old geometric LOW selection: disproved with two points, lambda = 3 pi,
  n = 0 by `not_legacySelectionLow` (standard axioms only). The repaired
  interface requires lambda <= pi and a nonzero chart reference.
- The low staircase cap now requires fractional part < 1/2; `big` is no
  longer unrelated to the strip.
- Capped LP infeasibility is not structural inconsistency; the delta
  clamp and warm-cache identity bug are recorded in the historical lane
  reports.

## Verification and completion gate

`verification/ProofAudit.lean` explicitly prints both unconditional root
statements and their transitive axioms. It also audits the integrated
supporting results. `verification/axiom-audit.txt` records the latest
output. A green Lake build with a lower-root `sorryAx` is not completion.

Completion requires both unconditional root halves, original-problem
correspondence including every N >= 3, no missing proof hidden in an
extra hypothesis, standard-only root axiom closures, a reproducible
pinned public commit, and a complete-proof reference PR under the awards
repository's contribution rules.

See `INTEGRATION_AUDIT_20260922.md` for source revisions and the detailed
scope audit. Older handoffs and `FINAL_DAG.md` are historical snapshots;
this file supersedes their current-status claims.
