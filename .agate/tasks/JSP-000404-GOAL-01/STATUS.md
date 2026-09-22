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

## P0-bridge (DONE) — geometry → `Base3CellData` at s=3

`Jsp000404/Base3Bridge.lean` (new, imported by root module):

- `linRep_oangle_eq_angle_or_pi_sub`: projective sweep between two
  direction reps at center `i` equals `∠` or `π−∠`. Uses the vector
  `Orientation.angle_eq_abs_oangle_toReal` (works for arbitrary
  `o : Orientation`, unlike the affine version which is pinned to
  `positiveOrientation` and needs `Module.Oriented`).
- `cycGaps_pair`: sorted 2-row has gaps `[b−a, π−(b−a)]`.
- `other1/other2`: the two non-self indices in `Fin 3`;
  `erase_finRange_eq` gives the row `[o1,o2]` after erase+sort.
- `rowScore_eq_gapScore_arcs`: `rowScore = g(∠ᵢ)+g(π−∠ᵢ)` — both
  cyclic gaps are genuine triangle arcs, so legality transfers.
- `base3CellData`: `ext i = ⌊(π−∠ᵢ)/λ⌋₊`, `k i = rowScore` satisfies
  all four fields from `Section4Legality` alone. `ext_pos` uses
  `∠ᵢ ≤ π−λ`; `top_requires_sat` uses `⌊∠/λ⌋+⌊(π−∠)/λ⌋ ≤ ⌊π/λ⌋ = n`;
  `ext_budget` uses `Σ∠ᵢ = π` (affine triangle sum) → `Σext ≤ 2(n+δ)`.
- `base3_potential_le` (δ<1/2 → `≤2^n`),
  `base3_potential_le_big` (`≤5·2^{n−2}` uniform).
- Axioms: `[propext, Classical.choice, Quot.sound]` only. No sorry.
- `lake build`: PASS (3262 jobs).

## Representation decision (P1)

Geometry rows ARE the closed angle system: `directionRow` keeps the
s−1 direction reps per center, `cycGaps` gives real consecutive arcs,
`erase_directionRow` already proves deletion = sub-configuration row.
No separate abstract `AngleSystem` class needed — the bridge is
`Section4Legality` directly. P2 = `erase_directionRow` (already
proved) + merge legality transfer; P3 = `sum_potential_erase` /
`removable_iff` (already proved in `Deletion.lean`).

Remaining sorry inventory (pre-existing, on prize path):
`Section4Legality.staircase_of_legality` (the optimization crux),
`Deletion.lean:1294,1304`, `GeometricDeletion.lean:629`,
`MainTheorem.lean:58,66`.
