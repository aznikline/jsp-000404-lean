# MIXED_TWO_IN_CENTRAL — build & evidence

Scope: `Jsp000404/MixedTwoInCentral.lean` — the five-point mixed two-in
central-insertion exclusion for the high-regime R=3 row.

## Theorems delivered

- `mixed_two_in_central`: five points, saturated anchor, `P,Q,R`
  defect-2, `H` defect ≥ 3; `P → H` short-first, `R → H` short-last.
  For `u = φ_HP`, `w = φ_HR`, `z = φ_HQ` the position `u < z < w` is
  impossible. Proof: consumes `five_point_high_receiver_not_full_in`
  (Q cannot also send a short chord to H) → non-short bounds
  `z − θ_Q ≥ λ`, `θ_Q + π − z ≥ λ`; then all six actual `Up`-branches.
  Two cross-row chains: (leaf 2) `P` zero-merge forces a sole scoring
  gap `≥ (n−1)λ`, `Q` both-end-big forces span `≤ β`, forcing two
  adjacent big gaps in `R`; leaf 4 is the independent mirror.
- `two_in_mixed_central_exclusion` (consumer): combines
  `two_in_mixed_ge_three` (`c_H ≥ 3`), `two_in_mixed_between`
  (`c_H > 3` forces `u < z < w`), `mixed_two_in_central`, and the
  actual direction distinctness hypotheses `z ≠ u`, `z ≠ w` to give
  `c_H = 3 ∧ (z < u ∨ w < z)`.

Honesty note: direction distinctness `z ≠ u`, `z ≠ w` is carried as an
explicit hypothesis; discharging it from legality is an open side-task.

## Axiom check

`#print axioms` for both theorems:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no new axioms.

## Builds

- `lake build Jsp000404.MixedTwoInCentral`: PASS (8964 jobs; the file
  itself ~114s at `maxHeartbeats 1600000` on the central theorem).
- Full root `lake build`: PASS, 9005 jobs, exit code 0.
  Command: `lake build` at repo root `D:/op/sunyuchen/jsp-000404-pc02`.
  Raw output: `MIXED_TWO_IN_CENTRAL_BUILD_LOG.txt` (same directory).
  Includes `Jsp000404.lean` importing `Jsp000404.MixedTwoInCentral`.

## Remaining warnings (non-fatal)

- `unusedSectionVars`: `C` auto-included but unused in `fin4_cover`,
  `not_short_witness_bounds`, `linScore4` (helper lemmas; `C` is in the
  `variable`s of the section and needed elsewhere).
- `push_neg` deprecation warnings (codebase style, matches existing
  files).
- `unusedTactic`: two `push_cast` calls flagged as no-ops.

## Open (explicitly not closed)

- Same-side two-in (`two_in_F_above`/`two_in_L_below` position already
  pinned; exclusion not attempted).
- Mixed outer `c_H = 3` realisation (whether the surviving position is
  geometrically realisable — NOT excluded).
- `z = u` / `z = w` collinearity discharge from legality.
- 0/1-in receivers, low-defect endpoints, R=4, general `m`, M3/M4.
- Five-point `R ≤ 2` is NOT closed.
- Air independent challenge: PENDING (no delegation channel).
