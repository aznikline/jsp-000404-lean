import Jsp000404.Gadget

/-!
# Gadget selection — lane A (LOW): the open combinatorial step

This file pins down, in compiling Lean, the *exact* proposition that
remains unproved in the LOW lane:

    GadgetSelectionLow s n  :  every mode-A-consistent skeleton with
        W(d) > 2 admits a valid gadget of bound ≥ 1/2 (score ≥ 1).

The reduction `GadgetSelectionLow → δ ≥ 1/2` is fully proved here
(`selection_low_sound`), so the whole LOW lane reduces to the single
combinatorial existence statement.

## Definitions

* `VertexData.kexp v = Σ_g max (q_{v,g} − 1) 0` — the checker exponent
  (`generic_model.q_tuples` enforces `Σ max(q−1,0) = k_v`, `Σq ≤ n`).
* `Skeleton.d n v = (n−1) − kexp v` — the deficit `d_v`.
* `Skeleton.W n = Σ_v 2^{−d_v}` — the dyadic mass, computed in `ℚ`.
* `Skeleton.Consistent n` — existence of a real remainder assignment
  `(r, δ)` satisfying mode A with `0 ≤ δ < 1` (realizability).
* `GadgetSelectionLow / GadgetSelectionHigh` — the selection
  propositions (`bound ≥ 1/2` resp. `bound ≥ 1`).

## Empirical status (see `notes/LANE_A.md`)

CHECKER-VALIDATED over the full `s = 4` corpus and extended-cap
evaluator runs; the Lean statement uses the extended cap language of
`Gadget.lean` (`CapKind.low`), which is needed for completeness —
without it, feasible-looking phantoms (LP bound `δ ≥ 1`) fall
through the gadget grammar.
-/

namespace Jsp404

open Finset

namespace VertexData

/-- Checker exponent at a vertex: `k_v = Σ_g max (q_g − 1) 0`. -/
def kexp {s : ℕ} (v : VertexData s) : ℤ :=
  ∑ g, max (v.q g - 1) 0

end VertexData

/-- Deficit at `v`: `d_v = (n−1) − k_v`. -/
def Skeleton.d {s : ℕ} (sk : Skeleton s) (n : ℕ) (v : Fin s) : ℤ :=
  (n : ℤ) - 1 - (sk.vtx v).kexp

/-- Dyadic mass `W(d) = Σ_v 2^{−d_v}` (exact rational value). -/
def Skeleton.W {s : ℕ} (sk : Skeleton s) (n : ℕ) : ℚ :=
  ∑ v : Fin s, (2 : ℚ) ^ (-(sk.d n v))

/-- Mode-A consistency (realizability): a real remainder assignment
exists with `0 ≤ δ < 1`.  Skeletons for which the LP is infeasible
already below `δ = 1` ("phantoms") or for every `δ` are excluded. -/
def Skeleton.Consistent {s : ℕ} (sk : Skeleton s) (n : ℕ) : Prop :=
  ∃ (r : Fin s → Fin (s - 1) → ℝ) (δ : ℝ),
    0 ≤ δ ∧ δ < 1 ∧ ModeA n sk r δ

/-- The LOW selection proposition — the open combinatorial theorem:

    `W(d) > 2` ⇒ every consistent skeleton admits a valid gadget of
    bound `≥ 1/2` (score `≥ 1`, i.e. `δ ≥ 1/2`).

Contrapositive: no score-1 gadget ⇒ `W ≤ 2`. -/
def GadgetSelectionLow (s n : ℕ) : Prop :=
  ∀ sk : Skeleton s, sk.Consistent n → 2 < sk.W n →
    ∃ g : Gadget s, g.Valid n sk ∧ (1 : ℚ) / 2 ≤ g.bound n sk

/-- The HIGH selection proposition (lane B): `W > 5/2` forces a
score-≥2 gadget (`δ ≥ 1`).  Stated for symmetry; unproved. -/
def GadgetSelectionHigh (s n : ℕ) : Prop :=
  ∀ sk : Skeleton s, sk.Consistent n → (5 : ℚ) / 2 < sk.W n →
    ∃ g : Gadget s, g.Valid n sk ∧ (1 : ℚ) ≤ g.bound n sk

/-- A rational gadget bound of `≥ 1/2` unpacks to the capacity
inequality `(cc + uu)/2 ≤ K − Bcap − CC` used by `gadget_ge_half`. -/
theorem bound_half_unfold {s : ℕ} (g : Gadget s) {n : ℕ}
    {sk : Skeleton s}
    (hb : (1 : ℚ) / 2 ≤ g.bound n sk) :
    (((g.cc n sk : ℤ) + (g.uu : ℤ) : ℤ) : ℝ) / 2
      ≤ ((g.K n sk - g.Bcap n sk - g.CC n sk : ℤ) : ℝ) := by
  have hb' := hb
  unfold Gadget.bound at hb'
  split_ifs at hb' with hden
  · norm_num at hb'
  · have hden' : (0 : ℚ) < (g.cc n sk : ℚ) + (g.uu : ℚ) :=
      lt_of_not_ge hden
    rw [le_div_iff₀ hden'] at hb'
    -- hb' : (1/2) * (cc+uu) ≤ num   (all rationals, num : ℤ cast)
    have hQ : ((((g.cc n sk : ℤ) + (g.uu : ℤ) : ℤ)) : ℚ) / 2
        ≤ ((g.K n sk - g.Bcap n sk - g.CC n sk : ℤ) : ℚ) := by
      have hcc : ((g.cc n sk : ℚ) + (g.uu : ℚ))
          = (((g.cc n sk : ℤ) + (g.uu : ℤ) : ℤ) : ℚ) := by
        push_cast; ring
      rw [hcc] at hb'
      linarith
    exact_mod_cast hQ

/-- A rational gadget bound of `≥ 1` unpacks to the capacity
inequality `cc + uu ≤ K − Bcap − CC` used by `gadget_ge_one`. -/
theorem bound_one_unfold {s : ℕ} (g : Gadget s) {n : ℕ}
    {sk : Skeleton s}
    (hb : (1 : ℚ) ≤ g.bound n sk) :
    (((g.cc n sk : ℤ) + (g.uu : ℤ) : ℤ) : ℝ)
      ≤ ((g.K n sk - g.Bcap n sk - g.CC n sk : ℤ) : ℝ) := by
  have hb' := hb
  unfold Gadget.bound at hb'
  split_ifs at hb' with hden
  · norm_num at hb'
  · have hden' : (0 : ℚ) < (g.cc n sk : ℚ) + (g.uu : ℚ) :=
      lt_of_not_ge hden
    rw [le_div_iff₀ hden'] at hb'
    have hQ : (((g.cc n sk : ℤ) + (g.uu : ℤ) : ℤ) : ℚ)
        ≤ ((g.K n sk - g.Bcap n sk - g.CC n sk : ℤ) : ℚ) := by
      have hcc : ((g.cc n sk : ℚ) + (g.uu : ℚ))
          = (((g.cc n sk : ℤ) + (g.uu : ℤ) : ℤ) : ℚ) := by
        push_cast; ring
      rw [hcc] at hb'
      linarith
    exact_mod_cast hQ

/-- Soundness of the LOW reduction: the selection proposition
implies the level-1 δ-bound on every consistent `W > 2` skeleton.
This is the complete lane-A theorem modulo `GadgetSelectionLow`. -/
theorem selection_low_sound {s n : ℕ} (hsel : GadgetSelectionLow s n)
    {sk : Skeleton s} {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hW : 2 < sk.W n) : (1 : ℝ) / 2 ≤ δ := by
  obtain ⟨g, hV, hb⟩ := hsel sk ⟨r, δ, hδ0, hδ1, hA⟩ hW
  apply g.gadget_ge_half n sk hA hV
  have hcap := bound_half_unfold g hb
  push_cast at hcap ⊢
  linarith

/-- Soundness of the HIGH reduction (lane B counterpart). -/
theorem selection_high_sound {s n : ℕ}
    (hsel : GadgetSelectionHigh s n)
    {sk : Skeleton s} {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hW : (5 : ℚ) / 2 < sk.W n) : (1 : ℝ) ≤ δ := by
  obtain ⟨g, hV, hb⟩ := hsel sk ⟨r, δ, hδ0, hδ1, hA⟩ hW
  apply g.gadget_ge_one n sk hA hV
  have hcap := bound_one_unfold g hb
  push_cast at hcap ⊢
  linarith

end Jsp404

#print axioms Jsp404.selection_low_sound
#print axioms Jsp404.selection_high_sound
