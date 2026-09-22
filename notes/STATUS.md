# JSP-000404 — consolidated status

Updated 2026-09-22 after the goal integration audit. **PARTIAL COVERAGE.**
The full arbitrary-N theorem and the prize submission are not complete.

## Current proof boundary

| Obligation | Status | Evidence |
|---|---|---|
| Every N >= 3: sharp upper construction, both bands | PROVED | `UpperBound.sendov_upper`; every epsilon > 0, exactly N distinct points |
| Genuine extremal quantity <= formula | PROVED | `UpperBound.alpha_le_alphaN` |
| N = 3 lower bound | PROVED | `Integration.sendov_lower_three` |
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
  `d66a6ab9cbe324d3353dbe7300880fb438838589`: three-center base,
  geometry/deletion bridges, induction, and Kraft equivalence.
- Wave-1/2 gadget semantics, signed caps, residual arithmetic, ghost
  counterexample, four-center high machinery and alignment invariant.

At the last remote check, `lane/l1-lowp` and `lane/v1-vacuum` still pointed
at their base `278c44c6e3c45df93de966402d76eb219d139291`. No new theorem
commit from those lanes was available to integrate. Their task status is
not inferred from a branch name or an old RUNNING label.

## Remaining global routes

1. **Gadget route:** arbitrary-size low and high consequences for faithful
   skeletons, followed by the geometry-to-skeleton adapter. `Proper`
   alone does not state nonnegative floor cells. The checker and formal
   model must have matching scope and boundary semantics.
2. **Geometric route:** prove the arbitrary-size `CertExists` progress
   lemma or the equivalent Kraft packing bound, handle n = 1, and wire
   the resulting staircase theorem into the lower-bound pipeline.

The s = 4 high reduction is proved conditional on `AllBadStrip`; it does
not settle arbitrary s. Finite enumerations do not prove the general
vacuum statement. Saturated-point lemmas constrain some profiles but do
not yet bound the total mass in every profile.

## Corrected and falsified interfaces

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
