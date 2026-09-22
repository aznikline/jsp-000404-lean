# JSP-000404 — consolidated status

Updated 2026-09-22 after the goal integration audit. **PARTIAL COVERAGE.**
The full arbitrary-N theorem and the prize submission are not complete.

## Current proof boundary

| Obligation | Status | Evidence |
|---|---|---|
| Every N >= 3: sharp upper construction, both bands | PROVED | `UpperBound.sendov_upper`; every epsilon > 0, exactly N distinct points |
| Genuine extremal quantity <= formula | PROVED | `UpperBound.alpha_le_alphaN` |
| N = 3, 4 lower bounds | PROVED | `sendov_lower_three`, `sendov_lower_four` |
| First-strip low/high capacities (n = 1) | PROVED | `SmallStrip.first_strip_capacity_low/high` |
| Geometric saturation count and half-strip threshold | PROVED | `SaturationPacking`, geometric saturation lemmas in `Induction` |
| Signed-cell normalization at arbitrary size | PROVED | `ProperGaps.ModeA.normalize`, `exists_nonnegative_model` |
| Full classification given geometric certificates | CONDITIONAL | `CertificateIntegration.sendov_alpha_eq_of_geometricCertificates` |
| Arbitrary-N lower bound given the capacity theorem | CONDITIONAL | `Integration.sendov_lower_of_selection` |
| Equality of genuine extremal quantity and formula given capacity | CONDITIONAL | `Integration.sendov_alpha_eq_of_selection` |
| Arbitrary-N lower bound with no extra hypothesis | OPEN | `MainTheorem.sendov_lower` still depends on `sorryAx` |
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
   lemma or the equivalent Kraft packing bound. The n = 1 boundary and
   final wiring are now proved: `GeometricCertificates` alone implies
   the full extremal equality. This premise itself remains OPEN.

The s = 4 high reduction is proved conditional on `AllBadStrip`; it does
not settle arbitrary s. Finite enumerations do not prove the general
vacuum statement. Saturated-point lemmas constrain some profiles but do
not yet bound the total mass in every profile.

Further proof details: `FIRST_STRIP_AND_CELLS.md` and `KRAFT_CRUX_AUDIT.md`.
The latter rejects an incorrect zero-saturation shortcut and records a
possible low-regime cone-cover route as a proof sketch only.

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
