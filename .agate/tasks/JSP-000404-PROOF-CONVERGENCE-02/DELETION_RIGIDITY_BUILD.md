# Deletion rigidity + two-in receiver normal form — build record

Module: `Jsp000404/DeletionRigidity.lean` (imported by `Jsp000404.lean`).

## What was proved (all new, `Jsp404` namespace)

Deletion rigidity (general `s`, scoped to `>=4` remaining points):
- `deletion_rigidity`: anchor `A` saturated, defect-2 rows `i, j`,
  delete `q ∉ {A,i,j}` → row `i` keeps score AND defect `2`.
  Uses `rowScore_add_three_le_of_two_saturated` on the reduced config:
  if `i` became saturated, `k'_j + 3 ≤ n` vs monotonicity `k'_j ≥ n−2`.
- `five_point_merge_zero_first/mid/last`: deleting each non-anchor
  chord position of `[θ, x₁, x₂, x₃]` gives merge gain `0` on the two
  adjacent gaps (anchor merge `(g₃,g₀)` not covered).
- `five_point_no_adjacent_big`: no two linearly adjacent gaps both
  `≥ λ`; Type II big-gap positions restricted to `{0,2},{0,3},{1,3}`;
  Type I unaffected.
- `not_both_big_of_mergeGain_zero`, `mergeGain_eq_two`
  (μ = 2 → both pieces `≥ λ` + floor carry).

Four-point equality (`five_point_delete_high_potential`):
- `R = 3`, delete high-defect row `h` → reduced potential
  `= 5 · 2^{n−2}` (anchor defect 1, three rigid defect-2 rows).
  Equality datum, NOT a contradiction.

Two-in receiver normal form (`linScore_split_low/mid/high` +
`two_in_*`):
- `two_in_F_row`/`two_in_L_row`/`two_in_mixed_row`: with exactly two
  incoming short chords, deleting the third source gives reduced score
  `n−2` (same side) or `n−3` (mixed); reinsertion splits exactly one
  gap and `c_h = c_h⁻ + μ`, `μ ≤ 2`. Outer gaps `< 2λ` give `μ = 0`
  via `mergeGain_eq_zero_of_lt`.
- `two_in_F_above`/`two_in_L_below`: defect `≥ 3` ⇒ third direction
  strictly beyond both received directions; `c_h = 2 + μ ≤ 4`.
- `two_in_mixed_between`: defect `> 3` ⇒ `z` strictly between the
  received directions; `c_h = 3 + μ`, `μ ∈ {1,2}`.
- `two_in_mixed_five`: `c_h = 5` ⇒ `μ = 2`, both pieces `≥ λ`, floor
  carry, `n ≥ 5`.
- `two_in_mixed_ge_three`: mixed two-in always has defect `≥ 3`.

Side-condition honesty: the two-in lemmas take explicit hypotheses
`dirRep h t ≠ dirRep h a/b` (distinct third direction), the window-side
`theta` comparisons, and the ordering `hord` between the two received
directions; all are dischargeable facts in intended consumers but are
NOT silently hidden.

## Axiom check

`lake env lean Jsp000404/DeletionRigidity.lean` — all 22 `#print axioms`
outputs are `[propext, Classical.choice, Quot.sound]`; NO `sorryAx`.

## Builds

- `lake build Jsp000404.DeletionRigidity`: PASS (8963 jobs).
- Full root `lake build` at tested code SHA
  `0be7313236cbad6ccae5b5e6a27de0704fd2581d` (evidence commit `c5a8d28`
  is documentation-only on top): PASS, 9004 jobs, exit code 0.
  NOTE: the raw build output for that run was not persisted to disk;
  the 9004-job result was recorded in-session only. The command was
  `lake build` at repo root. No further mechanical rerun was done for
  documentation purposes.
- Follow-up run (new code, includes `MixedTwoInCentral`): see
  `MIXED_TWO_IN_CENTRAL_BUILD.md` — `lake build` PASS, 9005 jobs,
  raw log in `MIXED_TWO_IN_CENTRAL_BUILD_LOG.txt`.

## Open (explicitly not closed)

- Step 4 of the packet: force a positive merge gain in some source row
  from the receiver insertion (`μ_h ≥ 1` vs all source `μ_i = 0`).
  PARTIALLY ADVANCED: the mixed two-in central-insertion mode is now
  excluded by `mixed_two_in_central` (see MIXED_TWO_IN_CENTRAL_BUILD.md).
  Remaining: same-side two-in, mixed outer `c_H = 3` realisation,
  0/1-in receivers, low-defect endpoints, R=4, general `m`.
- R=3 with 0/1 incoming at the high row; low-defect chain endpoints;
  R=4; general `m`; M3/M4.
- Air independent challenge: still PENDING (no delegation channel).

## Hook record

No `pre-commit`/`commit-msg`/`pre-push` hooks are installed in this
repo (only `.sample` files under the shared git dir); commits
`32869ea`, `7ab157b`, `f5a271f`, `0be7313` ran through plain `git
commit` with no hook output. No `--no-verify` was used in this batch.
