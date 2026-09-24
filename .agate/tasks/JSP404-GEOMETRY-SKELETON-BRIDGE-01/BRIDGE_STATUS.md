# BRIDGE_STATUS — JSP404-GEOMETRY-SKELETON-BRIDGE-01

Status: **complete as a Lean proof bridge** (module + full project build
green; no `sorry`/`sorryAx` in any bridge declaration).

Base: `9945ee8bd25ed3520aa89a063493cf3398e6f884`
Branch: `agent/jsp404-geometry-skeleton-bridge-01-owner`

## What is proved (all in `Jsp000404/GeomSkeleton.lean`, namespace `Jsp404`)

From `Section4Legality c lam` (`0 < lam`, `Injective c`, triangle angle
`≤ π − λ`), `e ≠ 0`, `2 ≤ s`, `lam ≤ π`, `⌊π/λ⌋₊ = n`:

| Obligation | Declaration | Content |
|---|---|---|
| construction | `fanOrder`, `other`, `selfIdx`, `rawBit`, `bridgeVtx`, `bridgeSkeleton`, `bridgeR`, `bridgeDelta` | `pos` = sorted rank of `selfIdx` in `dirRep` order; `bits` = lift flag; `q = ⌊gapAfter/λ⌋₊`; `r = gap/λ − q`; `δ = π/λ − n` |
| Proper | `bridgeSkeleton_proper` (:260) | distinct non-self slots get distinct `pos` (nodup `fanOrder` + `idxOf` injectivity) |
| `q`/`r` | `q_nonneg`, `r_nn` (:281), `r_lt_one` (:295), `q_add_r` (:307) | `0 ≤ r < 1` strict; `q + r = gapAfter/λ` |
| fan | `sum_gapAfter_eq_pi`, `fan_eq` (:342) | `Σr − δ = n − Σq` |
| arc telescoping | `sum_Ico_fin_eq`, `sum_Ico_gapAfter`, `arc_gapAfter` (:393), `arcSum_qr` (:458) | `Σ_{arc a b} gapAfter = \|d_{b'} − d_{a'}\|` incl. descending-pos (cyclic-cut) branch |
| lift bits | `oangle_eq_dirRep_sub_bit`, `oangle_sub_eq_dirRep`, `angle_eq_dirRep` | `Θ = ↑d − bit·π`; equal bits ⇒ `∠ = \|Δd\|`; differing ⇒ `∠ = π − \|Δd\|` |
| angle corr. | `angleExpr_eq` (:581), `angleExpr_eq_zero_of_selfIdx_eq` (:597) | `angleExpr = ∠(c a')(c x)(c b')/λ` for ALL `a b` incl. self slots; coincident `selfIdx` ⇒ `0` |
| ModeA | `geomSkeleton_modeA` (:621) | all six `ModeA` fields, self-slots handled via `other x` substitution |
| Consistent | `geomSkeleton_consistent` (:680) | `0 ≤ δ < 1` + `ModeA` |
| exponent | `bridgeVtx_kexp` (:707) | `kexp = ↑rowScore` |
| defect | `bridgeSkeleton_d` (:725) | `d = ↑rowDefect − 1` |
| weight | `bridgeSkeleton_W` (:739) | `W = potential / 2^{n−1}` (ℚ) — exact `W/K` factor |
| packaging | `gadgetSelection_of_selectionP` (:776) | `(∀ s n, GadgetSelectionLowP s n) → (∀ s n, GadgetSelectionHighP s n) → GadgetSelection` |

## Axiom audit

`#print axioms` (recorded in `GeomSkeletonRegress.lean:239–250`):
`bridgeSkeleton_proper`, `angleExpr_eq`, `geomSkeleton_modeA`,
`geomSkeleton_consistent`, `bridgeVtx_kexp`, `bridgeSkeleton_d`,
`bridgeSkeleton_W`, `gadgetSelection_of_selectionP` all depend on
**`[propext, Classical.choice, Quot.sound]` only — no `sorryAx`**.

## What remains open (explicit, not silently assumed)

`GadgetSelectionLowP` / `GadgetSelectionHighP`
(`GadgetCounterexample.lean:341,346`) stay open.  The packaging theorem
takes them as `∀ s n` hypotheses and uses only the *proved* soundness
reductions `selection_low_soundP` / `selection_high_soundP`.  No
`GadgetSelection`/`CertExists`/`KraftPacking` hypothesis feeds back into
the bridge.  The pre-existing `sorry` in `MainTheorem.lean:11`
(`sendov_lower`, arbitrary-size certificate) is unrelated and unchanged.

## Regression module

`Jsp000404/GeomSkeletonRegress.lean` — see `REGRESSION_MANIFEST.json`.
Covers square config, degenerate `s = 2` rows, cyclic-cut arc branch,
lift-bit +/− controls, `q`/`r` bounds, floor/`δ`/`n` bindings, exact
`W/K` factor, self-slot domain+reduction.

## Files

- `Jsp000404/GeomSkeleton.lean` — the bridge (883 lines, new).
- `Jsp000404/GeomSkeletonRegress.lean` — regression + axiom audit (new).
- `Jsp000404.lean` — root imports for both modules.
- `.agate/tasks/JSP404-GEOMETRY-SKELETON-BRIDGE-01/CONTRACT_MAP.md` — G0.
- `.agate/tasks/JSP404-GEOMETRY-SKELETON-BRIDGE-01/{BRIDGE_STATUS,REGRESSION_MANIFEST,ASSUMPTION_AUDIT,LEAD_FINAL}` — this packet.
