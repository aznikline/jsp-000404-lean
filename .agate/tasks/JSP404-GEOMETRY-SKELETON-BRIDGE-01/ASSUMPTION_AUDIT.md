# ASSUMPTION_AUDIT — JSP404-GEOMETRY-SKELETON-BRIDGE-01

Rule enforced: nothing beyond `Section4Legality` + the stated interface
bindings was assumed; every condition not derivable from existing
legality is listed as an open obligation.  Target model unchanged.

## Source assumptions consumed (hypotheses of the bridge theorems)

| assumption | where used | derivable from `Section4Legality`? |
|---|---|---|
| `0 < lam` | `Section4Legality.lam_pos` field | yes — it IS legality |
| `Function.Injective c` | `Section4Legality.inj`; used for `other`/`selfIdx` distinctness and triangle nondegeneracy | yes — legality |
| `triAngle` bound `∠ ≤ π − λ` | `ang_le` in `geomSkeleton_modeA` | yes — legality |
| `e ≠ 0` | `dirRep` well-definedness, `oangle` laws, `bits` lift | **interface** — chart reference, required by the consumer (`GadgetSelection.low/high` also take `e ≠ 0`) |
| `2 ≤ s` | `other x` needs a non-self index; `Proper` domain `Fin (s−1)` | **interface** — `V.forest_len` supplies it in packaging; `s < 2` is vacuous (`Skeleton 1` uninhabited) |
| `lam ≤ π` | `1 ≤ n` (from `⌊π/λ⌋ = n`), hence `0 ≤ n − 1 + δ` for `ang_nn`/self-slot `ang_le` | **interface** — same hypothesis as `GadgetSelection.low/high` |
| `⌊π/λ⌋₊ = n` | `rowCells ≤ n` (`rowCells_directionRow_le_of_floor_eq`), `0 ≤ δ`, `δ < 1` | **interface** — strip binding, same as consumer |
| `δ = π/λ − n` | definitional `bridgeDelta` | definitional |
| `2 ≤ s` for `s = 4` | square fixture | `decide` |

## Derived (not assumed)

- `pos` injectivity on non-self slots → `Skeleton.Proper` (nodup sorted
  `fanOrder`, `List.idxOf` injectivity).  Duplicate `dirRep` values are
  handled by `insertionSort` index order — no strictness assumed.
- `0 ≤ r < 1`, `q + r = gapAfter/λ`, `Σr − δ = n − Σq`,
  `Σ gapAfter = π` — floor algebra + `gapAfter_sum`.
- `arc` sums = `|d_{b'} − d_{a'}|` — finite Ico telescoping.
- `bits` semantics: `Θ_a = ↑(d_a) − bit_a·π`; equal bits ⇒ direct arc
  angle, differing ⇒ complementary `n + δ − arc` — from
  `linRep_class` + `oangle_sub`/`angle_eq_abs_oangle_toReal`.
- Self slots (`a = x` or `b = x` in `ang_le`/`ang_nn`): `selfIdx`
  substitutes `other x`; `angleExpr x x b` is a *genuine* geometric
  angle at `other x`; coincident substitution gives `expr = 0`
  (`angleExpr_eq_zero_of_selfIdx_eq`).  Nothing assumed away.
- `kexp = rowScore`, `d = rowDefect − 1`, `W = potential/2^{n−1}` —
  proved equalities, exact factors.

## Open obligations (explicit — NOT assumed by the bridge)

| obligation | consumer | status |
|---|---|---|
| `GadgetSelectionLowP s n` | `gadgetSelection_of_selectionP` (`hlow` hypothesis) → `GadgetSelection.low` | open (proof-convergence scope); bridge consumes it only as a `∀ s n` hypothesis via `selection_low_soundP` |
| `GadgetSelectionHighP s n` | `gadgetSelection_of_selectionP` (`hhigh`) → `GadgetSelection.high` | open; same conditional treatment via `selection_high_soundP` |
| `sendov_lower` arbitrary-size certificate | `MainTheorem.lean:11` | pre-existing `sorry`, unrelated to this task, unchanged |

## Weakening check

- `Section4Legality` unchanged (source not strengthened).
- `Skeleton`/`VertexData`/`ModeA`/`Proper`/`Consistent`/`W`/`d`/`kexp`
  unchanged (target not weakened).
- `GadgetSelection` unchanged; `gadgetSelection_of_selectionP` is a
  strictly conditional packaging theorem — the open propositions appear
  as its hypotheses, never as axioms.
- `#print axioms`: all bridge declarations depend on
  `[propext, Classical.choice, Quot.sound]` only (recorded in
  `GeomSkeletonRegress.lean` tail).
