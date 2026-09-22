import Jsp000404.DebtChain

/-!
# Chain witness — frozen interface for `DebtSelection`

Pure-arithmetic packaging of `debt_residual_ge_half`.  A witness is
a finite data object (real vectors) whose `Valid`ity implies
`δ ≥ 1/2`.  Both observed certificate families — two-fan
alternating chains and one-fan chains ending in a δ-dependent cap —
instantiate the same `ResidualWitness`.

## Counting criterion (verified against the 75-instance corpus)

For a two-fan chain the capacity condition unrolls to

    `#charged + Σ bT j ≥ B_L + B_R + B_cap + 1`

where `B_v = d_v + 1 - pos_v` is the endpoint remainder budget
(`Σr_v = B_v + δ`), `bT_j = -cT_j` the per-link triangle slack, and
`B_cap` the constant part of the cap bound.  Endpoint budgets enter
as a *cost*: low-budget endpoints (saturated fans, `Σq_v ≈ n`) are
cheaper to terminate on.  All 75 mapped instances satisfy the
inequality with equality.

## Design note — `DebtSelection` (statement only, unproven)

Target theorem, once the skeleton layer exists:

    -- if `∑ i, (2:ℝ) ^ (-(d i : ℤ)) > 2` then every mode-A-legal
    -- skeleton admits a valid `ResidualWitness` on its restriction.

Equivalently, via the auxiliary fan-graph formulation: the
skeleton's triangle-link graph contains a positive-score path
between two fans (or a fan and a cap), where edge weight is
`charged + bT` and endpoints cost `B_L + B_R`.  The open question
is why `W(d) > 2` forces such a path — candidate routes are an
inclusion-minimal overfull block or a path-dual potential
certificate summing to `W ≤ 2`.
-/

namespace Jsp404

open Finset

/-- Data for a packaged residual certificate.  `Valid` packages the
five hypotheses of `debt_residual_ge_half`.  Producing the data and
discharging `Valid` is the combinatorics layer's job. -/
structure ResidualWitness where
  P : ℝ
  U : ℝ
  C : ℝ
  K : ℝ
  c : ℝ
  u : ℝ
  B : ℝ
  δ : ℝ

def ResidualWitness.Valid (w : ResidualWitness) : Prop :=
  w.P - w.U - w.c * w.δ = w.C
    ∧ w.K ≤ w.P
    ∧ w.U ≤ w.B + w.u * w.δ
    ∧ 0 < w.c + w.u
    ∧ (w.c + w.u) / 2 ≤ w.K - w.B - w.C

theorem ResidualWitness.ge_half (w : ResidualWitness)
    (h : w.Valid) : (1 : ℝ) / 2 ≤ w.δ :=
  debt_residual_ge_half h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- **Threshold-parameterized validity.**  `Valid` hard-codes the
`τ = 1/2` capacity condition; the high regime needs `τ = 1`.  Any
witness whose capacity slack dominates `τ·(c+u)` forces `δ ≥ τ`.
Note: `w.δ` is only *the* δ of the geometric system when the
construction binds it — `ge_of` gives no conclusion about the
original system unless the caller passes that δ. -/
theorem ResidualWitness.ge_of (w : ResidualWitness) {τ : ℝ}
    (hres : w.P - w.U - w.c * w.δ = w.C)
    (hP : w.K ≤ w.P) (hU : w.U ≤ w.B + w.u * w.δ)
    (hc : 0 < w.c + w.u)
    (hcap : τ * (w.c + w.u) ≤ w.K - w.B - w.C) : τ ≤ w.δ :=
  debt_residual_ge hres hP hU hc hcap

/-- Data for a two-fan telescoping chain of length `m`. -/
structure DebtChainWitness where
  m : ℕ
  S : ℕ → ℝ
  D : ℕ → ℝ
  E : ℕ → ℝ
  cT : ℕ → ℝ
  lL : ℝ
  lR : ℝ
  cL : ℝ
  cR : ℝ
  K : ℝ
  δ : ℝ

def DebtChainWitness.Valid (w : DebtChainWitness) : Prop :=
  w.S w.m = 0
    ∧ w.S 0 + w.lL - w.δ = w.cL
    ∧ (∑ j ∈ Finset.range w.m, w.E j) + w.lR - w.δ = w.cR
    ∧ (∀ j ∈ Finset.range w.m,
        w.S j - w.D j - w.S (j + 1) + w.E j = w.cT j)
    ∧ w.K ≤ ∑ j ∈ Finset.range w.m, w.D j
    ∧ 0 ≤ w.lL
    ∧ 0 ≤ w.lR
    ∧ w.cL + w.cR - ∑ j ∈ Finset.range w.m, w.cT j ≤ w.K - 1

theorem DebtChainWitness.ge_half (w : DebtChainWitness)
    (h : w.Valid) : (1 : ℝ) / 2 ≤ w.δ :=
  debt_chain_ge_half h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2

end Jsp404

#print axioms Jsp404.ResidualWitness.ge_half
#print axioms Jsp404.DebtChainWitness.ge_half
