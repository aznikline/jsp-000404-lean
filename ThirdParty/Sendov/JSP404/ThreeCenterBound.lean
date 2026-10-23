import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# The arithmetic bound for three centers

This module proves only the three-center arithmetic case. The hypotheses on the
normalized positive angles are explicit; no geometric reduction to three centers
is assumed. Natural-number subtraction implements the positive part in the exponent.
-/

namespace JSP404

/-- The two saturated floor contributions attached to a normalized angle. -/
noncomputable def centerExponent (q a : ℝ) : ℕ :=
  (⌊q * a⌋₊ - 1) + (⌊q * (1 - a)⌋₊ - 1)

theorem mul_le_sub_one_of_normalized_cap {q a : ℝ} (hq : 0 < q)
    (hcap : a ≤ 1 - 1 / q) : q * a ≤ q - 1 := by
  have hh := mul_le_mul_of_nonneg_left hcap hq.le
  have hc : q * (1 - 1 / q) = q - 1 := by field_simp
  rwa [hc] at hh

/-- The elementary floor estimate underlying the exponent bound. -/
theorem floor_pair_exponent_bound {n : ℕ} {δ x y : ℝ}
    (hn : 2 ≤ n) (hδ : δ < 1) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsum : x + y = (n : ℝ) + δ) (hcap : x ≤ (n : ℝ) - 1 + δ) :
    (⌊x⌋₊ - 1) + (⌊y⌋₊ - 1) ≤ n - 1 ∧
      ((⌊x⌋₊ - 1) + (⌊y⌋₊ - 1) = n - 1 → x ≤ δ) := by
  have hfx := Nat.floor_le hx
  have hfy := Nat.floor_le hy
  have hsum_floor : ⌊x⌋₊ + ⌊y⌋₊ ≤ n := by
    have hh : ((⌊x⌋₊ + ⌊y⌋₊ : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hh' : ⌊x⌋₊ + ⌊y⌋₊ < n + 1 := by exact_mod_cast hh
    omega
  have hfloorx : ⌊x⌋₊ ≤ n - 1 := by
    have hh : (⌊x⌋₊ : ℝ) < (n : ℝ) := by linarith
    have hh' : ⌊x⌋₊ < n := by exact_mod_cast hh
    omega
  constructor
  · omega
  · intro heq
    have hyfloor : ⌊y⌋₊ = n := by omega
    rw [hyfloor] at hfy
    linarith

/-- A center exponent is at most `n-1`; reaching this level forces a small angle. -/
theorem centerExponent_bound {n : ℕ} {δ a : ℝ}
    (hn : 2 ≤ n) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (ha : 0 < a) (hcap : a ≤ 1 - 1 / ((n : ℝ) + δ)) :
    centerExponent ((n : ℝ) + δ) a ≤ n - 1 ∧
      (centerExponent ((n : ℝ) + δ) a = n - 1 → ((n : ℝ) + δ) * a ≤ δ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : 0 < (n : ℝ) + δ := by linarith
  have hfrac : 0 < 1 / ((n : ℝ) + δ) := one_div_pos.mpr hq
  have ha1 : a < 1 := by linarith
  have hqa : ((n : ℝ) + δ) * a ≤ (n : ℝ) - 1 + δ := by
    have hh := mul_le_sub_one_of_normalized_cap hq hcap
    linarith
  exact floor_pair_exponent_bound hn hδ1 (mul_nonneg hq.le ha.le)
    (mul_nonneg hq.le (by linarith)) (by ring) hqa

private theorem two_pow_pred_eq (n : ℕ) (hn : 2 ≤ n) :
    2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
  have he : n - 1 = (n - 2) + 1 := by omega
  rw [he, pow_succ, Nat.mul_comm]

private theorem two_pow_eq_four (n : ℕ) (hn : 2 ≤ n) :
    2 ^ n = 4 * 2 ^ (n - 2) := by
  have he : n = (n - 2) + 2 := by omega
  calc
    2 ^ n = 2 ^ ((n - 2) + 2) := by rw [← he]
    _ = 4 * 2 ^ (n - 2) := by rw [pow_add]; ring

/-- Three exponents bounded by `n-1`, with at most one at the upper level. -/
theorem three_powers_le_two_pow_of_at_most_one_high
    {n k₁ k₂ k₃ : ℕ} (hn : 2 ≤ n)
    (h₁ : k₁ ≤ n - 1) (h₂ : k₂ ≤ n - 1) (h₃ : k₃ ≤ n - 1)
    (h₁₂ : ¬ (k₁ = n - 1 ∧ k₂ = n - 1))
    (h₁₃ : ¬ (k₁ = n - 1 ∧ k₃ = n - 1))
    (h₂₃ : ¬ (k₂ = n - 1 ∧ k₃ = n - 1)) :
    2 ^ k₁ + 2 ^ k₂ + 2 ^ k₃ ≤ 2 ^ n := by
  have hlow (k : ℕ) (h : k ≤ n - 1) (hne : k ≠ n - 1) :
      2 ^ k ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hhigh : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := two_pow_pred_eq n hn
  rw [two_pow_eq_four n hn]
  by_cases he₁ : k₁ = n - 1
  · have hl₂ := hlow k₂ h₂ (fun h => h₁₂ ⟨he₁, h⟩)
    have hl₃ := hlow k₃ h₃ (fun h => h₁₃ ⟨he₁, h⟩)
    rw [he₁, hhigh]
    omega
  · have hl₁ := hlow k₁ h₁ he₁
    by_cases he₂ : k₂ = n - 1
    · have hl₃ := hlow k₃ h₃ (fun h => h₂₃ ⟨he₂, h⟩)
      rw [he₂, hhigh]
      omega
    · have hl₂ := hlow k₂ h₂ he₂
      have hl₃ : 2 ^ k₃ ≤ 2 * 2 ^ (n - 2) := by
        rw [← hhigh]
        exact Nat.pow_le_pow_right (by decide) h₃
      omega

/-- Three exponents bounded by `n-1`, with at most two at the upper level. -/
theorem three_powers_le_five_of_not_all_high
    {n k₁ k₂ k₃ : ℕ} (hn : 2 ≤ n)
    (h₁ : k₁ ≤ n - 1) (h₂ : k₂ ≤ n - 1) (h₃ : k₃ ≤ n - 1)
    (hnot : ¬ (k₁ = n - 1 ∧ k₂ = n - 1 ∧ k₃ = n - 1)) :
    2 ^ k₁ + 2 ^ k₂ + 2 ^ k₃ ≤ 5 * 2 ^ (n - 2) := by
  have hhigh : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := two_pow_pred_eq n hn
  have hhi (k : ℕ) (h : k ≤ n - 1) : 2 ^ k ≤ 2 * 2 ^ (n - 2) := by
    rw [← hhigh]
    exact Nat.pow_le_pow_right (by decide) h
  have hlow (k : ℕ) (h : k ≤ n - 1) (hne : k ≠ n - 1) :
      2 ^ k ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hh₁ := hhi k₁ h₁
  have hh₂ := hhi k₂ h₂
  have hh₃ := hhi k₃ h₃
  by_cases he₁ : k₁ = n - 1
  · by_cases he₂ : k₂ = n - 1
    · have hl₃ := hlow k₃ h₃ (fun h => hnot ⟨he₁, he₂, h⟩)
      omega
    · have hl₂ := hlow k₂ h₂ he₂
      omega
  · have hl₁ := hlow k₁ h₁ he₁
    omega

/-- When `δ < 1/2`, two of the three centers cannot both have the largest exponent. -/
theorem three_centers_not_two_high {n : ℕ} {δ a b c : ℝ}
    (hn : 2 ≤ n) (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (ha : 0 < a) (hb : 0 < b) (hsum : a + b + c = 1)
    (hcapA : a ≤ 1 - 1 / ((n : ℝ) + δ))
    (hcapB : b ≤ 1 - 1 / ((n : ℝ) + δ))
    (hcapC : c ≤ 1 - 1 / ((n : ℝ) + δ)) :
    ¬ (centerExponent ((n : ℝ) + δ) a = n - 1 ∧
      centerExponent ((n : ℝ) + δ) b = n - 1) := by
  rintro ⟨heA, heB⟩
  have hδ1 : δ < 1 := by linarith
  have haSmall := (centerExponent_bound hn hδ0 hδ1 ha hcapA).2 heA
  have hbSmall := (centerExponent_bound hn hδ0 hδ1 hb hcapB).2 heB
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : 0 < (n : ℝ) + δ := by linarith
  have hcBound := mul_le_sub_one_of_normalized_cap hq hcapC
  have hsumq : ((n : ℝ) + δ) * a + ((n : ℝ) + δ) * b +
      ((n : ℝ) + δ) * c = (n : ℝ) + δ := by
    calc
      _ = ((n : ℝ) + δ) * (a + b + c) := by ring
      _ = (n : ℝ) + δ := by rw [hsum, mul_one]
  linarith

/-- For all `0 ≤ δ < 1`, not all three centers can have the largest exponent. -/
theorem three_centers_not_all_high {n : ℕ} {δ a b c : ℝ}
    (hn : 2 ≤ n) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hsum : a + b + c = 1)
    (hcapA : a ≤ 1 - 1 / ((n : ℝ) + δ))
    (hcapB : b ≤ 1 - 1 / ((n : ℝ) + δ))
    (hcapC : c ≤ 1 - 1 / ((n : ℝ) + δ)) :
    ¬ (centerExponent ((n : ℝ) + δ) a = n - 1 ∧
      centerExponent ((n : ℝ) + δ) b = n - 1 ∧
      centerExponent ((n : ℝ) + δ) c = n - 1) := by
  rintro ⟨heA, heB, heC⟩
  have haSmall := (centerExponent_bound hn hδ0 hδ1 ha hcapA).2 heA
  have hbSmall := (centerExponent_bound hn hδ0 hδ1 hb hcapB).2 heB
  have hcSmall := (centerExponent_bound hn hδ0 hδ1 hc hcapC).2 heC
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsumq : ((n : ℝ) + δ) * a + ((n : ℝ) + δ) * b +
      ((n : ℝ) + δ) * c = (n : ℝ) + δ := by
    calc
      _ = ((n : ℝ) + δ) * (a + b + c) := by ring
      _ = (n : ℝ) + δ := by rw [hsum, mul_one]
  linarith

/-- The stronger three-center count in the range `0 ≤ δ < 1/2`. -/
theorem three_center_bound_small_delta {n : ℕ} {δ a b c : ℝ}
    (hn : 2 ≤ n) (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hsum : a + b + c = 1)
    (hcapA : a ≤ 1 - 1 / ((n : ℝ) + δ))
    (hcapB : b ≤ 1 - 1 / ((n : ℝ) + δ))
    (hcapC : c ≤ 1 - 1 / ((n : ℝ) + δ)) :
    2 ^ centerExponent ((n : ℝ) + δ) a +
      2 ^ centerExponent ((n : ℝ) + δ) b +
      2 ^ centerExponent ((n : ℝ) + δ) c ≤ 2 ^ n := by
  have hδ1 : δ < 1 := by linarith
  apply three_powers_le_two_pow_of_at_most_one_high hn
    (centerExponent_bound hn hδ0 hδ1 ha hcapA).1
    (centerExponent_bound hn hδ0 hδ1 hb hcapB).1
    (centerExponent_bound hn hδ0 hδ1 hc hcapC).1
  · exact three_centers_not_two_high hn hδ0 hδhalf ha hb hsum hcapA hcapB hcapC
  · exact three_centers_not_two_high hn hδ0 hδhalf ha hc (by linarith [hsum])
      hcapA hcapC hcapB
  · exact three_centers_not_two_high hn hδ0 hδhalf hb hc (by linarith [hsum])
      hcapB hcapC hcapA

/-- The three-center count valid throughout `0 ≤ δ < 1`, in particular the upper half. -/
theorem three_center_bound {n : ℕ} {δ a b c : ℝ}
    (hn : 2 ≤ n) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hsum : a + b + c = 1)
    (hcapA : a ≤ 1 - 1 / ((n : ℝ) + δ))
    (hcapB : b ≤ 1 - 1 / ((n : ℝ) + δ))
    (hcapC : c ≤ 1 - 1 / ((n : ℝ) + δ)) :
    2 ^ centerExponent ((n : ℝ) + δ) a +
      2 ^ centerExponent ((n : ℝ) + δ) b +
      2 ^ centerExponent ((n : ℝ) + δ) c ≤ 5 * 2 ^ (n - 2) := by
  exact three_powers_le_five_of_not_all_high hn
    (centerExponent_bound hn hδ0 hδ1 ha hcapA).1
    (centerExponent_bound hn hδ0 hδ1 hb hcapB).1
    (centerExponent_bound hn hδ0 hδ1 hc hcapC).1
    (three_centers_not_all_high hn hδ0 hδ1 ha hb hc hsum hcapA hcapB hcapC)

end JSP404
