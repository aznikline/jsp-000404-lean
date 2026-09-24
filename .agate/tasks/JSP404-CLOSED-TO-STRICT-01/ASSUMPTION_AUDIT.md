# ASSUMPTION_AUDIT — JSP404-CLOSED-TO-STRICT-01

Rule enforced: the normalization is proved for *abstract*
Proper/ModeA closed-remainder models. Nothing about geometry,
realizability, defect profile, or gadget transport is assumed or claimed.
`Skeleton`/`VertexData`/`ModeA`/`Proper`/`Consistent`/`W`/`d`/`kexp`/
`angleExpr` definitions unchanged; no upstream file modified except the
root import list (`Jsp000404.lean`).

## Hypotheses consumed per theorem

| theorem | hypotheses | notes |
|---|---|---|
| `Skeleton.strictify_gap` | none | definitional: `+ε` and `−ε` cancel |
| `Skeleton.strictR_nn` | `∀ x g, 0 ≤ r x g` | needed: `r'` keeps `r` off the boundary |
| `Skeleton.strictR_lt_one` | `∀ x g, r x g ≤ 1` | `r = 1 ↦ 0`; else `r < 1` by `≤ ∧ ≠` |
| `Skeleton.strictify_q_ge` / `q_nonneg` | none / `0 ≤ q` | `ε ∈ {0,1}` |
| `Skeleton.strictify_of_rem_eq_one` | `r x g = 1` | boundary profile |
| `Skeleton.strictify_neg_one` | `q = -1`, `r = 1` | `(−1,1) ↦ (0,0)` |
| `Skeleton.strictify_angle` | none | pos/bits/gaps preserved |
| `ModeA.strictify` | `ModeA n sk r δ` | uses `r_nn`, `r_le`; no `Proper`, no `δ` hypothesis needed |
| `Skeleton.strictify_q_nonneg_of_modeA` | `ModeA`, `Proper`, `0 ≤ δ` | via `ModeA.q_nonnegative_of_strict` on the strict model — `Proper` and `0 ≤ δ` enter only here (through `gap_nonnegative`) |
| `strictify_nonneg_eq_self` | `ModeA`, `Proper`, `0 ≤ δ` | composition order: strictify already nonneg |
| `nonnegative_strictify_eq` | `ModeA`, `Proper`, `0 ≤ δ` | commutation; `negative_q_boundary` identifies `q = -1, r = 1` |
| `strictify_kexp_ge` / `d_le` / `W_le_strictify_W` | none | pure monotone bookkeeping on `q` |
| `strictify_eq_self_of_strict`, `strictR_eq_fun_of_strict` | `∀ x g, r x g < 1` | strict-input identity |
| `strictify_idempotent`, `strictR_idempotent` | `∀ x g, r x g ≤ 1` | `strictR r` is strict |
| `exists_strict_model` | `Proper`, `Consistent n` | unpacks `0 ≤ δ < 1`, `ModeA`; returns strict + nonneg + `W ≤ W'` |
| `capacity_of_strict_models` | bound over proper strict models; `Proper`, `ModeA` | `W sk ≤ W sk' ≤ B`; **no** `0 ≤ δ` needed |
| `capacity_of_strict_nonneg_models` | bound over proper strict + `q ≥ 0` models; `Proper`, `ModeA`, `0 ≤ δ` | `q' ≥ 0` discharged by `strictify_q_nonneg_of_modeA` |

## Boundary coverage (`r = 1` handled for every `q`)

| profile | strictify | kexp effect |
|---|---|---|
| `(q, 1)`, `q ≥ 1` | `(q+1, 0)` | `max(q−1,0) → max(q,0)` = **+1** (W grows) |
| `(0, 1)` | `(1, 0)` | `0 → 0` (unchanged) |
| `(−1, 1)` | `(0, 0)` | `0 → 0` (same target as `nonnegative`) |
| `(q, r)`, `r < 1` | `(q, r)` | unchanged |

Note: under `ModeA + Proper + 0 ≤ δ`, `q < 0` forces `(−1, 1)`
(`negative_q_boundary`), so the table covers all realizable cells and
`q'` is automatically `≥ 0` on strictify output.

## What is NOT assumed / not claimed

- No defect-profile or unique-saturation preservation.
- No model→geometry realizability adapter; `GeomSkeleton` bridge not
  invoked in this direction.
- No gadget witness transport: `Gadget.Valid`/`bound` read `q`, which
  strictify changes on `r = 1` cells; capacity is transferred via the
  `W` comparison, not by transporting certificates.
- No `SelectionP`/`MainTheorem`/`GadgetSelection*P` progress.
- `W` is proved non-decreasing and CAN strictly increase — the transfer
  direction `W sk ≤ W sk' ≤ B` is the sound one; the converse
  (`W sk' ≤ W sk`) is false in general (fixture `bSk3`: `7/2 < 4`).

## Axiom check

`#print axioms` on all key declarations: `[propext, Classical.choice,
Quot.sound]` only. The `noncomputable` markers on `strictify`/`strictR`/
`bR3` come from `Real.decidableEq`/`Real.instDivInvMonoid` — classical
decidability of `r = 1` and `1/2 : ℝ`, i.e. `Classical.choice`, already
in the standard axiom set. No `sorryAx` anywhere in the new module.
