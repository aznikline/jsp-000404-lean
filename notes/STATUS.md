# JSP-000404 — consolidated status

Updated 2026-09-22 after the goal integration audit. **PARTIAL COVERAGE.**
The full arbitrary-N theorem and the prize submission are not complete.

## Current proof boundary

| Obligation | Status | Evidence |
|---|---|---|
| Every N >= 3: sharp upper construction, both bands | PROVED | `UpperBound.sendov_upper`; every epsilon > 0, exactly N distinct points |
| Genuine extremal quantity <= formula | PROVED | `UpperBound.alpha_le_alphaN` |
| Every N from 3 through 8: lower bounds | PROVED | `sendov_lower_three`, `sendov_lower_four`, `sendov_lower_five_to_eight` |
| Every N from 3 through 8: genuine extremal equality | PROVED | `SmallAngleLower.sendov_alpha_eq_le_eight` |
| First-strip low/high capacities (n = 1) | PROVED | `SmallStrip.first_strip_capacity_low/high` |
| Second-strip LOW capacity (n = 2), every profile | PROVED | `SecondStrip.potential_le_four_of_second_strip_low` |
| Second-strip HIGH capacity (n = 2), every profile | PROVED | `SecondStripHigh.potential_le_five_of_second_strip` |
| Arbitrary-size LOW capacity when a saturated center exists | PROVED | `OneSaturatedLow.potential_le_two_pow_of_saturated`; no certificate premise |
| Arbitrary-size HIGH capacity when two saturated centers exist | PROVED | `TwoSaturatedHigh.potential_le_high_of_two_saturated`; any original anchors/chart |
| Two saturated centers, at least four centers: every other defect >= 3 | PROVED | `TwoSaturatedDeficit.rowDefect_ge_three_of_two_saturated`; actual original rows |
| Full-row restriction to selected rays / local three-term bounds | PROVED | `TriangleRestriction`; these do not imply the global sum bound |
| Geometric saturation count and half-strip threshold | PROVED | `SaturationPacking`, geometric saturation lemmas in `Induction` |
| Signed-cell normalization at arbitrary size | PROVED | `ProperGaps.ModeA.normalize`, `exists_nonnegative_model` |
| Full classification given geometric certificates | CONDITIONAL | `CertificateIntegration.sendov_alpha_eq_of_geometricCertificates` |
| Arbitrary-N lower bound given the capacity theorem | CONDITIONAL | `Integration.sendov_lower_of_selection` |
| Equality of genuine extremal quantity and formula given capacity | CONDITIONAL | `Integration.sendov_alpha_eq_of_selection` |
| N >= 9 lower bound with no extra hypothesis | OPEN | `MainTheorem.sendov_lower` still depends on `sorryAx` |
| Final complete-proof submission | NOT READY | Requires the unconditional lower bound and completion audit |

Sharpness means arbitrarily close actual configurations, not an assumed
exact minimizing configuration. `Statement.lean` contains the formula and
point-configuration definitions. The upper constructions are attributed
imports from superpilot69's pinned MIT-licensed development, connected by
new local proofs; see `ThirdParty/Sendov/README.md`.

## Integrated material

- User-designated trunk: `lane/integration` at
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

At the last remote check, `lane/l1-lowp` and `lane/v1-vacuum` still pointed
at their base `278c44c6e3c45df93de966402d76eb219d139291`. No new theorem
commit from those lanes was available to integrate. Their task status is
not inferred from a branch name or an old RUNNING label.

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
