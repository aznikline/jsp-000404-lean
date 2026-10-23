import JSP404.Basic
import Mathlib.Tactic

/-!
# An explicit five-point counterexample to the linked problem-page formula

The five vertices of a rational-coordinate house-shaped pentagon have every
angle at most `3 * π / 4`, strictly less than the claimed `4 * π / 5`.
This is a counterexample to the transcribed formula, not a proof of Sendov's
complete classification of the extremal angles.
-/

noncomputable section

open scoped RealInnerProductSpace
open Real

namespace JSP404

/-- An algebraic sufficient condition for a vector angle of at most 135 degrees. -/
theorem angle_le_three_pi_div_four_of_inner
    (u v : Point)
    (h : 0 ≤ ⟪u, v⟫ ∨
      2 * ⟪u, v⟫ ^ 2 ≤ ⟪u, u⟫ * ⟪v, v⟫) :
    InnerProductGeometry.angle u v ≤ 3 * π / 4 := by
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hcos : Real.cos (3 * π / 4) = -(Real.sqrt 2 / 2) := by
    rw [show 3 * π / 4 = π - π / 4 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_four]
  have hratio : -(Real.sqrt 2 / 2) ≤ ⟪u, v⟫ / (‖u‖ * ‖v‖) := by
    rcases h with h | h
    · exact le_trans (neg_nonpos.mpr (by positivity)) (div_nonneg h (by positivity))
    · by_cases hzero : ‖u‖ * ‖v‖ = 0
      · rw [hzero, div_zero]
        exact neg_nonpos.mpr (by positivity)
      have hpos : 0 < ‖u‖ * ‖v‖ := lt_of_le_of_ne (by positivity) (Ne.symm hzero)
      apply (le_div_iff₀ hpos).2
      have hsquare : (Real.sqrt 2 / 2 * (‖u‖ * ‖v‖)) ^ 2 =
          (‖u‖ * ‖v‖) ^ 2 / 2 := by
        rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
      have hbound : ⟪u, v⟫ ^ 2 ≤
          (Real.sqrt 2 / 2 * (‖u‖ * ‖v‖)) ^ 2 := by
        rw [hsquare]
        nlinarith
      have hlower := (abs_le_of_sq_le_sq' hbound (by positivity)).1
      nlinarith
  unfold InnerProductGeometry.angle
  calc
    Real.arccos (⟪u, v⟫ / (‖u‖ * ‖v‖)) ≤ Real.arccos (Real.cos (3 * π / 4)) :=
      Real.arccos_le_arccos (by rwa [hcos])
    _ = 3 * π / 4 := Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])

/-- Rational-coordinate vertices; the last three form the roof of a house. -/
def housePoint : Fin 5 → Point :=
  ![!₂[-1, -1], !₂[1, -1], !₂[1, 1], !₂[0, 2], !₂[-1, 1]]

theorem housePoint_injective : Function.Injective housePoint := by
  intro i j h
  have h0 := congrArg (fun p : Point => p 0) h
  have h1 := congrArg (fun p : Point => p 1) h
  fin_cases i <;> (try fin_cases j) <;> norm_num [housePoint] at *

/-- The algebraic check includes repeated points as well as the 60 distinct triples. -/
theorem housePoint_angle_le (i j k : Fin 5) :
    EuclideanGeometry.angle (housePoint i) (housePoint j) (housePoint k) ≤ 3 * π / 4 := by
  apply angle_le_three_pi_div_four_of_inner
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [housePoint, PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

def house : Finset Point := Finset.univ.image housePoint

theorem house_card : house.card = 5 := by
  rw [house, Finset.card_image_of_injective _ housePoint_injective]
  simp

theorem house_angle_le {a b c : Point} (ha : a ∈ house) (hb : b ∈ house)
    (hc : c ∈ house) : EuclideanGeometry.angle a b c ≤ 3 * π / 4 := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
  exact housePoint_angle_le i j k

theorem three_pi_div_four_lt_four_pi_div_five : 3 * π / 4 < 4 * π / 5 := by
  linarith [Real.pi_pos]

/-- The explicit five-point configuration bounds the actual geometric threshold. -/
theorem alpha_five_le_three_pi_div_four : alpha 5 ≤ 3 * π / 4 := by
  apply alpha_le_of_configuration (by norm_num) house_card
  intro a ha b hb c hc _ _ _
  exact house_angle_le ha hb hc

/-- In particular the displayed problem-page value for five points is impossible. -/
theorem alpha_five_lt_four_pi_div_five : alpha 5 < 4 * π / 5 :=
  alpha_five_le_three_pi_div_four.trans_lt three_pi_div_four_lt_four_pi_div_five

theorem alpha_five_ne_four_pi_div_five : alpha 5 ≠ 4 * π / 5 :=
  ne_of_lt alpha_five_lt_four_pi_div_five

/-- The claimed 144-degree guarantee fails, with `house` as a concrete witness. -/
theorem not_guaranteed_five_four_pi_div_five : ¬ Guaranteed 5 (4 * π / 5) := by
  intro h
  obtain ⟨a, ha, b, hb, c, hc, _, _, _, hang⟩ := h house house_card
  exact (not_le.mpr three_pi_div_four_lt_four_pi_div_five)
    (hang.trans (house_angle_le ha hb hc))

end JSP404
