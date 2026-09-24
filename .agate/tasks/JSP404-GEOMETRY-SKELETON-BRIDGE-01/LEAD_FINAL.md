# LEAD_FINAL — JSP404-GEOMETRY-SKELETON-BRIDGE-01

## Verdict

**Bridge delivered as proved Lean code.**  A legal planar configuration
(`Section4Legality c lam`, `e ≠ 0`, `2 ≤ s`, `lam ≤ π`, `⌊π/λ⌋₊ = n`)
maps into the gadget pipeline's actual `Skeleton`/`Proper`/`ModeA`
model with exponent, scale, and weight correspondences *proved*, not
proposed.  No source strengthening, no target weakening.

## Shipped

| item | location |
|---|---|
| geometry→skeleton adapter + all correspondence proofs | `Jsp000404/GeomSkeleton.lean` (883 lines) |
| regression fixture + `#print axioms` audit | `Jsp000404/GeomSkeletonRegress.lean` |
| root imports | `Jsp000404.lean:35–36` |
| contract map (G0) | `.agate/tasks/JSP404-GEOMETRY-SKELETON-BRIDGE-01/CONTRACT_MAP.md` |
| status / regression manifest / assumption audit | same directory |

## Key proved facts (all `Jsp404.`)

- `bridgeSkeleton_proper` — `pos` distinct on non-self slots.
- `q_nonneg`, `r_nn`, `r_lt_one`, `q_add_r` — canonical `q`/`r`
  decomposition, `0 ≤ r < 1` strict.
- `sum_gapAfter_eq_pi`, `fan_eq` — fan telescoping
  `Σr − δ = n − Σq` with `δ = π/λ − n`.
- `arc_gapAfter`, `arcSum_qr` — arc sums equal `|d_{b'} − d_{a'}|`,
  both `pos`-order branches (cyclic cut).
- `oangle_eq_dirRep_sub_bit`, `angle_eq_dirRep` — lift-bit algebra:
  `Θ = ↑d − bit·π`; equal bits → direct arc, differing → `n+δ−arc`.
- `angleExpr_eq` — `angleExpr = ∠/λ` for **all** slots, self-slots
  included; `angleExpr_eq_zero_of_selfIdx_eq` for coincident
  substitution.  Self-slot handling is explicit via `other`/`selfIdx`.
- `geomSkeleton_modeA`, `geomSkeleton_consistent` — `ModeA` complete,
  `0 ≤ δ < 1`.
- `bridgeVtx_kexp` (`kexp = rowScore`), `bridgeSkeleton_d`
  (`d = rowDefect − 1`), `bridgeSkeleton_W`
  (`W = potential / 2^{n−1}` over ℚ — the exact `W/K` factor).
- `gadgetSelection_of_selectionP` — `GadgetSelection` from
  `(∀ s n, GadgetSelectionLowP s n)` + `(∀ s n, GadgetSelectionHighP s n)`
  via proved `selection_low/high_soundP`.

## Verification performed

- `lake build Jsp000404.GeomSkeletonRegress` — clean.
- `lake build` — **Build completed successfully (8997 jobs)**, root
  import live.
- `#print axioms` on all bridge declarations + square fixtures:
  `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**.
- No `sorry`/`admit` in `GeomSkeleton.lean`; the only project `sorry`
  remains the pre-existing `MainTheorem.lean:11` (`sendov_lower`),
  out of scope.

## Open obligations (explicit — consumed conditionally, never assumed)

- `GadgetSelectionLowP s n`, `GadgetSelectionHighP s n`
  (`GadgetCounterexample.lean:341,346`) remain open.  The packaging
  theorem takes them as `∀ s n` hypotheses; downstream consumers get a
  conditional `GadgetSelection`, matching how
  `staircaseBound_of_selection`/`count_bound_of_selection` already
  consume `GadgetSelection`.
- Interface bindings actually needed beyond `Section4Legality`:
  `e ≠ 0`, `2 ≤ s`, `lam ≤ π`, `⌊π/λ⌋₊ = n` — the same interface the
  consumer `GadgetSelection.low/high` already requires.

## Git

- Commit `6faa37e` on `agent/jsp404-geometry-skeleton-bridge-01-owner`,
  pushed; remote readback `refs/heads/… = 6faa37e4` matches local HEAD.
- Files: `Jsp000404/GeomSkeleton.lean` (new),
  `Jsp000404/GeomSkeletonRegress.lean` (new), `Jsp000404.lean` (2
  imports), `.agate/tasks/JSP404-GEOMETRY-SKELETON-BRIDGE-01/*` (4
  artifacts + this file).

## Handoff notes

- The conditional `GadgetSelection` produced by
  `gadgetSelection_of_selectionP` slots directly into
  `staircaseBound_of_selection` → `count_bound_of_selection` →
  `sendov_*_of_selection`; closing `GadgetSelectionLowP/HighP` is the
  only remaining gap to the unconditional chain (proof-convergence
  scope, untouched here).
