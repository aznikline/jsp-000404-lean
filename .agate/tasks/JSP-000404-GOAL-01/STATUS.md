# JSP-000404 GOAL-01 — Owner status

Branch: `agent/jsp404-angle-cert-goal-01-owner`
North star: arbitrary-N Sendov count bound closed in Lean kernel, no sorry.

## Phase status

| Phase | Content | State |
|---|---|---|
| P0 | s=3 closed-form base (`Base3.lean`) | **DONE** — kernel-verified |
| P1 | `AngleSystem` + geometry→abstraction bridge | IN PROGRESS |
| P2 | erase/merge preserves `AngleSystem` | pending |
| P3 | potential deletion identity hookup | pending |
| P4 | **Cert Lemma** — sole math crux | open |
| P5 | induction → `StaircaseBound` → `sendov_count_bound` | pending |

## P0 (DONE)

`Jsp000404/Base3.lean`:
- `Base3CellData n δ` — `ext`/`k` + L1 `ext_pos`, L2 `top_requires_sat`,
  L3 `ext_budget` (real form of `Σext ≤ ⌊2(n+δ)⌋`), `k_le`.
- `base3_low`: `δ < 1/2 → Σᵢ 2^{kᵢ} ≤ 2^n` (sharp).
- `base3_high`: `δ < 1 → Σᵢ 2^{kᵢ} ≤ 5·2^{n-2}` (= `2^n+2^{n-2}`).
- Axioms: `[propext, Classical.choice, Quot.sound]` only. No sorry.
- Note: high bound holds for ALL δ<1; the phase transition is entirely
  the sharper `2^n` at δ<1/2.

## Key falsified candidates (do not retry)

- global `Σ 2^{kᵢ}Eᵢ ≥ F` — fails (optimal wE = F−2 on feasible, 56/572)
- weak `wE ≥ F−s+1` — fails (deficit 8 > slack 3, δ=3/4)
- min-k cert, extremal(min∪max)-k cert — fail at δ=3/4
- max-gap vertex CertA∨CertC; boundary-emitter; ρ/σ terminal cycle;
  zero-emitter charge map; any pure k-level selection rule.
- Cert existence is incidence/carry-structural, 1600+/1600+ verified.

## Lead's parallel lane (origin/master, tools/+notes/HANDOFF.md)

ABCEDF/gadget route: dyadic `W = Σ2^{(n−1)−kᵢ}`; crux
`gadgetSelection_{low,high}` — complementary challenger to Cert Lemma.
Confirmed facts: δ_min ∈ {0,½,1,inf}; W>5/2 ⇒ δ_min≥1.
