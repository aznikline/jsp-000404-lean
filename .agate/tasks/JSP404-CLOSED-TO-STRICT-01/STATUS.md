# STATUS — JSP404-CLOSED-TO-STRICT-01

Status: **complete** (new module `Jsp000404/StrictRemainderNormalization.lean`
builds green as part of the full project build; no `sorry`/`sorryAx` in any
new declaration).

Base: `6e1e2484c60fc1e6f74615dd6e4f3d8110f36fb5` (`origin/lane/integration`)
Branch: `agent/jsp404-closed-to-strict-01-air`

## What is proved (all in `Jsp000404/StrictRemainderNormalization.lean`, namespace `Jsp404`)

Per cell `(q, r) ↦ (q + ε, r − ε)` with `ε = 1` iff `r = 1`; i.e.
`(q, 1) ↦ (q + 1, 0)`, all other cells unchanged.

| Obligation | Declaration | Content |
|---|---|---|
| construction | `Skeleton.strictify`, `Skeleton.strictR` | `q' = q + ε`, `r' = r − ε`; `pos`/`bits`/`n`/`δ` untouched (noncomputable defs: `Decidable (r = 1)` on ℝ is classical) |
| Proper | `Skeleton.strictify_proper` | `Proper` carries over verbatim (pos unchanged) |
| gap | `Skeleton.strictify_gap` | `q' + r' = q + r` cell-wise |
| remainder bounds | `Skeleton.strictR_nn`, `strictR_lt_one`, `strictR_le_one` | `0 ≤ r'` from `0 ≤ r`; `r' < 1` from `r ≤ 1` |
| cell monotonicity | `Skeleton.strictify_q_ge`, `strictify_q_nonneg` | `q ≤ q'`; `q ≥ 0 → q' ≥ 0` |
| boundary | `strictify_of_rem_eq_one`, `strictify_neg_one` | `(q,1) ↦ (q+1,0)`; `(−1,1) ↦ (0,0)` |
| angles | `Skeleton.strictify_angle` | `angleExpr` identical before/after |
| ModeA | `ModeA.strictify` | `ModeA n sk r δ → ModeA n (sk.strictify r) (sk.strictR r) δ` — all six fields |
| q' ≥ 0 for free | `strictify_q_nonneg_of_modeA` | under `ModeA + Proper + 0 ≤ δ`, strictified skeleton already nonnegative (via `q_nonnegative_of_strict` on the strict model) |
| commute with ProperGaps | `strictify_nonneg_eq_self`, `nonnegative_strictify_eq` | `(sk.strictify r).nonnegative = sk.strictify r`; `sk.nonnegative.strictify (sk.normalizedR r) = sk.strictify r` |
| W | `Skeleton.strictify_kexp_ge`, `strictify_d_le`, `W_le_strictify_W` | `kexp` non-decreasing, `d` non-increasing, `W` non-decreasing (NOT equality) |
| strict input | `strictify_eq_self_of_strict`, `strictR_eq_fun_of_strict`, `strictify_q_eq_self`, `strictR_eq_self` | already-strict model unchanged |
| idempotency | `strictify_idempotent`, `strictR_idempotent` | second pass is the identity (needs `r ≤ 1`) |
| packaging | `exists_strict_model` | proper + consistent ⇒ ∃ proper strict + nonneg + consistent model with `W sk ≤ W sk'` |
| capacity transfer | `capacity_of_strict_models` | `W ≤ B` over proper strict-remainder ModeA models ⇒ `W ≤ B` over proper closed-remainder ModeA models |
| capacity variant | `capacity_of_strict_nonneg_models` | bound may also assume `q ≥ 0` (available under `0 ≤ δ`) |

## Regressions (fixture `bSk3`, `bR3`, `s = 3`, `n = 2`)

- `(1,1) ↦ (2,0)` (`b_v0g0_q`, `b_v0g0_r`) — the W-increasing profile
- `(0,1) ↦ (1,0)` (`b_v0g1_q`) — `r = 1` at `q = 0`
- `(−1,1) ↦ (0,0)` (`b_v1g0_q`, `b_v1g0_r`) — negative boundary repaired
- `(3,0)` (`b_v1g1`), `(0,0)` (`b_v2g1`) — `r = 0` unchanged
- `(2,1/2)` (`b_v2g0`) — interior remainder unchanged
- `b_strictR_zero` — zero remainder ⇒ strictify = identity
- `bSk3_kexp`, `bSk3_strictify_kexp` — exponent bookkeeping `0,2,1 → 1,2,1`
- `bSk3_W`, `bSk3_strictify_W`, `bSk3_W_strictly_increases` — `W = 7/2 < 4 = W'`
- `bR3_closed`, `bSk3_strictR_strict` — fixture remainder is closed ⇒ strict

## Axiom audit

`#print axioms` (bottom of module): all 13 audited declarations —
`strictify_gap`, `strictR_lt_one`, `strictify_angle`, `ModeA.strictify`,
`strictify_q_nonneg_of_modeA`, `nonnegative_strictify_eq`,
`W_le_strictify_W`, `strictify_eq_self_of_strict`, `strictify_idempotent`,
`exists_strict_model`, `capacity_of_strict_models`,
`capacity_of_strict_nonneg_models`, `bSk3_W_strictly_increases` —
depend on `[propext, Classical.choice, Quot.sound]` only. No `sorryAx`.

## Build

- `lake build Jsp000404.StrictRemainderNormalization`: clean (1.3s, zero warnings in the new file).
- `lake build` (full project): **success**, 8998 jobs; warnings only
  pre-existing deprecations/lints in other modules.

## Proved vs transferred vs not claimed

- **Proved**: the strictification is a well-defined Proper/ModeA
  endomap on closed-remainder models at fixed `n`, `δ`, preserving every
  `angleExpr`, giving `0 ≤ r' < 1`, `q' ≥ 0` (under `0 ≤ δ`), and
  `W ≤ W'`.
- **Transferred**: capacity bound `W ≤ B` strict ⇒ closed
  (`capacity_of_strict_models`), and the strict+nonneg-premise variant.
- **Not claimed** (explicit non-goals, unchanged): defect profile or
  unique-saturation preservation; model→geometry realizability; gadget
  witness transport (`Gadget`/`Valid`/`bound` are defined over `q` —
  strictify changes `q`, so gadgets are not transported);
  `GadgetSelectionLowP`/`GadgetSelectionHighP`/`SelectionP`/`MainTheorem`
  progress. No change to `OneSaturatedHigh`/`ConeCorridor`/`K3bGeometry`,
  no G3 worktree touch.

## Review flag

Written by the air owner — flag for Lead's independent review before any
integration merge. Do NOT merge to `lane/integration` from this branch.
