import Jsp000404.MixedStarExclusion
import Jsp000404.S8Defs

set_option maxHeartbeats 40000000

/-!
# Extraction: eight-centre `SatChart` → `N8Model` (narrow core)

The `SatChart → N8Model` geometric bridge (n8T/n8σ/n8model and the
row-extraction lemmas) without the `S8Certs` certificate closure.
The three positional-class terminals remain in `S8Extraction`.
-/


namespace Jsp404

open Classical
open scoped EuclideanSpace

/-- A five-element list splits into its literals. -/
private theorem length_eq_five' {α : Type*} {l : List α}
    (h : l.length = 5) :
    ∃ a b c d e : α, l = [a, b, c, d, e] := by
  cases l with
  | nil => simp at h
  | cons a l' =>
    rw [List.length_cons] at h
    obtain ⟨b, c, d, e, rfl⟩ :=
      List.length_eq_four.mp (show l'.length = 4 by omega)
    exact ⟨a, b, c, d, e, rfl⟩

/-- A six-element list splits into its literals. -/
private theorem length_eq_six {α : Type*} {l : List α}
    (h : l.length = 6) :
    ∃ a b c d e f : α, l = [a, b, c, d, e, f] := by
  cases l with
  | nil => simp at h
  | cons a l' =>
    rw [List.length_cons] at h
    obtain ⟨b, c, d, e, f, rfl⟩ :=
      length_eq_five' (show l'.length = 5 by omega)
    exact ⟨a, b, c, d, e, f, rfl⟩

private theorem s7fl3 {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    ⌊g / lam⌋₊ = 3 ↔ 3 * lam ≤ g ∧ g < 4 * lam := by
  rw [Nat.floor_eq_iff (div_nonneg hg hlam.le)]
  constructor
  · rintro ⟨h1, h2⟩
    rw [le_div_iff₀ hlam] at h1; rw [div_lt_iff₀ hlam] at h2
    push_cast at h1 h2 ⊢; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    constructor
    · rw [le_div_iff₀ hlam]; exact_mod_cast h1
    · rw [div_lt_iff₀ hlam]; exact_mod_cast h2

private theorem s7fl2 {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    ⌊g / lam⌋₊ = 2 ↔ 2 * lam ≤ g ∧ g < 3 * lam := by
  rw [Nat.floor_eq_iff (div_nonneg hg hlam.le)]
  constructor
  · rintro ⟨h1, h2⟩
    rw [le_div_iff₀ hlam] at h1; rw [div_lt_iff₀ hlam] at h2
    push_cast at h1 h2 ⊢; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    constructor
    · rw [le_div_iff₀ hlam]; exact_mod_cast h1
    · rw [div_lt_iff₀ hlam]; exact_mod_cast h2

private theorem s7fl1 {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    ⌊g / lam⌋₊ ≤ 1 ↔ g < 2 * lam := by
  rw [show ⌊g / lam⌋₊ ≤ 1 ↔ ⌊g / lam⌋₊ < 2 from (Nat.lt_add_one_iff).symm,
    Nat.floor_lt (div_nonneg hg hlam.le), div_lt_iff₀ hlam]
  push_cast
  exact Iff.rfl

set_option maxHeartbeats 1200000 in
theorem rowSig2_8_of_linearScore_two {lam θ : ℝ} (hlam : 0 < lam)
    {x0 x1 x2 x3 x4 x5 : ℝ}
    (hord : θ ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ θ + Real.pi)
    (hsc : linearGapScore lam θ (θ + Real.pi) [x0, x1, x2, x3, x4, x5] = 2) :
    R2N4.RowSig2_8 lam Real.pi θ x0 x1 x2 x3 x4 x5 := by
  have hg0 : 0 ≤ (x0 - θ) := by linarith [hord.1]
  have hg1 : 0 ≤ (x1 - x0) := by linarith [hord.2.1]
  have hg2 : 0 ≤ (x2 - x1) := by linarith [hord.2.2.1]
  have hg3 : 0 ≤ (x3 - x2) := by linarith [hord.2.2.2.1]
  have hg4 : 0 ≤ (x4 - x3) := by linarith [hord.2.2.2.2.1]
  have hg5 : 0 ≤ (x5 - x4) := by linarith [hord.2.2.2.2.2.1]
  have hg6 : 0 ≤ (θ + Real.pi - x5) := by linarith [hord.2.2.2.2.2.2]
  have hsum : ((⌊(x0 - θ) / lam⌋₊ - 1) + (⌊(x1 - x0) / lam⌋₊ - 1) + (⌊(x2 - x1) / lam⌋₊ - 1) + (⌊(x3 - x2) / lam⌋₊ - 1) + (⌊(x4 - x3) / lam⌋₊ - 1) + (⌊(x5 - x4) / lam⌋₊ - 1) + (⌊(θ + Real.pi - x5) / lam⌋₊ - 1)) = 2 := by
    have h := hsc
    simp only [linearGapScore, gapScore] at h
    omega
  have b0 : ⌊(x0 - θ) / lam⌋₊ ≤ 3 := by omega
  have b1 : ⌊(x1 - x0) / lam⌋₊ ≤ 3 := by omega
  have b2 : ⌊(x2 - x1) / lam⌋₊ ≤ 3 := by omega
  have b3 : ⌊(x3 - x2) / lam⌋₊ ≤ 3 := by omega
  have b4 : ⌊(x4 - x3) / lam⌋₊ ≤ 3 := by omega
  have b5 : ⌊(x5 - x4) / lam⌋₊ ≤ 3 := by omega
  have b6 : ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 3 := by omega
  have key :
      (⌊(x0 - θ) / lam⌋₊ = 3 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 3 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ = 3 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 3 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ = 3 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ = 3 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ = 3) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ = 2 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ = 2 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧ ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ = 2 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ = 2 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ = 2 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ = 2 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧ ⌊(x4 - x3) / lam⌋₊ = 2 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ = 2 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ = 2 ∧ ⌊(x5 - x4) / lam⌋₊ = 2 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ = 2 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ = 2 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ = 2) := by
    by_cases q0 : ⌊(x0 - θ) / lam⌋₊ = 3
    · exact Or.inl ⟨q0, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · by_cases q1 : ⌊(x1 - x0) / lam⌋₊ = 3
      · exact Or.inr (Or.inl ⟨by omega, q1, by omega, by omega, by omega, by omega, by omega⟩)
      · by_cases q2 : ⌊(x2 - x1) / lam⌋₊ = 3
        · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, q2, by omega, by omega, by omega, by omega⟩))
        · by_cases q3 : ⌊(x3 - x2) / lam⌋₊ = 3
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, q3, by omega, by omega, by omega⟩)))
          · by_cases q4 : ⌊(x4 - x3) / lam⌋₊ = 3
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, q4, by omega, by omega⟩))))
            · by_cases q5 : ⌊(x5 - x4) / lam⌋₊ = 3
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, q5, by omega⟩)))))
              · by_cases q6 : ⌊(θ + Real.pi - x5) / lam⌋₊ = 3
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, by omega, q6⟩))))))
                ·
                  by_cases r0 : ⌊(x0 - θ) / lam⌋₊ = 2
                  ·
                    by_cases s1 : ⌊(x1 - x0) / lam⌋₊ = 2
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, s1, by omega, by omega, by omega, by omega, by omega⟩)))))))
                    ·
                      by_cases s2 : ⌊(x2 - x1) / lam⌋₊ = 2
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, by omega, s2, by omega, by omega, by omega, by omega⟩))))))))
                      ·
                        by_cases s3 : ⌊(x3 - x2) / lam⌋₊ = 2
                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, by omega, by omega, s3, by omega, by omega, by omega⟩)))))))))
                        ·
                          by_cases s4 : ⌊(x4 - x3) / lam⌋₊ = 2
                          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, by omega, by omega, by omega, s4, by omega, by omega⟩))))))))))
                          ·
                            by_cases s5 : ⌊(x5 - x4) / lam⌋₊ = 2
                            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, by omega, by omega, by omega, by omega, s5, by omega⟩)))))))))))
                            ·
                              have s6 : ⌊(θ + Real.pi - x5) / lam⌋₊ = 2 := by omega
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, by omega, by omega, by omega, by omega, by omega, s6⟩))))))))))))
                  ·
                    by_cases r1 : ⌊(x1 - x0) / lam⌋₊ = 2
                    ·
                      by_cases s2 : ⌊(x2 - x1) / lam⌋₊ = 2
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, r1, s2, by omega, by omega, by omega, by omega⟩)))))))))))))
                      ·
                        by_cases s3 : ⌊(x3 - x2) / lam⌋₊ = 2
                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, r1, by omega, s3, by omega, by omega, by omega⟩))))))))))))))
                        ·
                          by_cases s4 : ⌊(x4 - x3) / lam⌋₊ = 2
                          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, r1, by omega, by omega, s4, by omega, by omega⟩)))))))))))))))
                          ·
                            by_cases s5 : ⌊(x5 - x4) / lam⌋₊ = 2
                            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, r1, by omega, by omega, by omega, s5, by omega⟩))))))))))))))))
                            ·
                              have s6 : ⌊(θ + Real.pi - x5) / lam⌋₊ = 2 := by omega
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, r1, by omega, by omega, by omega, by omega, s6⟩)))))))))))))))))
                    ·
                      by_cases r2 : ⌊(x2 - x1) / lam⌋₊ = 2
                      ·
                        by_cases s3 : ⌊(x3 - x2) / lam⌋₊ = 2
                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, r2, s3, by omega, by omega, by omega⟩))))))))))))))))))
                        ·
                          by_cases s4 : ⌊(x4 - x3) / lam⌋₊ = 2
                          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, r2, by omega, s4, by omega, by omega⟩)))))))))))))))))))
                          ·
                            by_cases s5 : ⌊(x5 - x4) / lam⌋₊ = 2
                            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, r2, by omega, by omega, s5, by omega⟩))))))))))))))))))))
                            ·
                              have s6 : ⌊(θ + Real.pi - x5) / lam⌋₊ = 2 := by omega
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, r2, by omega, by omega, by omega, s6⟩)))))))))))))))))))))
                      ·
                        by_cases r3 : ⌊(x3 - x2) / lam⌋₊ = 2
                        ·
                          by_cases s4 : ⌊(x4 - x3) / lam⌋₊ = 2
                          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, r3, s4, by omega, by omega⟩))))))))))))))))))))))
                          ·
                            by_cases s5 : ⌊(x5 - x4) / lam⌋₊ = 2
                            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, r3, by omega, s5, by omega⟩)))))))))))))))))))))))
                            ·
                              have s6 : ⌊(θ + Real.pi - x5) / lam⌋₊ = 2 := by omega
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, r3, by omega, by omega, s6⟩))))))))))))))))))))))))
                        ·
                          by_cases r4 : ⌊(x4 - x3) / lam⌋₊ = 2
                          ·
                            by_cases s5 : ⌊(x5 - x4) / lam⌋₊ = 2
                            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, r4, s5, by omega⟩)))))))))))))))))))))))))
                            ·
                              have s6 : ⌊(θ + Real.pi - x5) / lam⌋₊ = 2 := by omega
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, r4, by omega, s6⟩))))))))))))))))))))))))))
                          ·
                            have r5 : ⌊(x5 - x4) / lam⌋₊ = 2 := by omega
                            have s6 : ⌊(θ + Real.pi - x5) / lam⌋₊ = 2 := by omega
                            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega, r5, s6⟩)))))))))))))))))))))))))))
  rw [s7fl3 hlam hg0, s7fl2 hlam hg0, s7fl1 hlam hg0, s7fl3 hlam hg1, s7fl2 hlam hg1, s7fl1 hlam hg1, s7fl3 hlam hg2, s7fl2 hlam hg2, s7fl1 hlam hg2, s7fl3 hlam hg3, s7fl2 hlam hg3, s7fl1 hlam hg3, s7fl3 hlam hg4, s7fl2 hlam hg4, s7fl1 hlam hg4, s7fl3 hlam hg5, s7fl2 hlam hg5, s7fl1 hlam hg5, s7fl3 hlam hg6, s7fl2 hlam hg6, s7fl1 hlam hg6] at key
  simpa only [R2N4.RowSig2_8, and_assoc] using key

set_option maxHeartbeats 1200000 in
theorem rowSig1_8_of_linearScore_one {lam θ : ℝ} (hlam : 0 < lam)
    {x0 x1 x2 x3 x4 x5 : ℝ}
    (hord : θ ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ θ + Real.pi)
    (hsc : linearGapScore lam θ (θ + Real.pi) [x0, x1, x2, x3, x4, x5] = 1) :
    R2N4.RowSig1_8 lam Real.pi θ x0 x1 x2 x3 x4 x5 := by
  have hg0 : 0 ≤ (x0 - θ) := by linarith [hord.1]
  have hg1 : 0 ≤ (x1 - x0) := by linarith [hord.2.1]
  have hg2 : 0 ≤ (x2 - x1) := by linarith [hord.2.2.1]
  have hg3 : 0 ≤ (x3 - x2) := by linarith [hord.2.2.2.1]
  have hg4 : 0 ≤ (x4 - x3) := by linarith [hord.2.2.2.2.1]
  have hg5 : 0 ≤ (x5 - x4) := by linarith [hord.2.2.2.2.2.1]
  have hg6 : 0 ≤ (θ + Real.pi - x5) := by linarith [hord.2.2.2.2.2.2]
  have hsum : ((⌊(x0 - θ) / lam⌋₊ - 1) + (⌊(x1 - x0) / lam⌋₊ - 1) + (⌊(x2 - x1) / lam⌋₊ - 1) + (⌊(x3 - x2) / lam⌋₊ - 1) + (⌊(x4 - x3) / lam⌋₊ - 1) + (⌊(x5 - x4) / lam⌋₊ - 1) + (⌊(θ + Real.pi - x5) / lam⌋₊ - 1)) = 1 := by
    have h := hsc
    simp only [linearGapScore, gapScore] at h
    omega
  have b0 : ⌊(x0 - θ) / lam⌋₊ ≤ 2 := by omega
  have b1 : ⌊(x1 - x0) / lam⌋₊ ≤ 2 := by omega
  have b2 : ⌊(x2 - x1) / lam⌋₊ ≤ 2 := by omega
  have b3 : ⌊(x3 - x2) / lam⌋₊ ≤ 2 := by omega
  have b4 : ⌊(x4 - x3) / lam⌋₊ ≤ 2 := by omega
  have b5 : ⌊(x5 - x4) / lam⌋₊ ≤ 2 := by omega
  have b6 : ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 2 := by omega
  have key :
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ = 2 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ = 2 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(x5 - x4) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x5) / lam⌋₊ = 2) := by
    by_cases q0 : ⌊(x0 - θ) / lam⌋₊ = 2
    · exact Or.inl ⟨q0, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · by_cases q1 : ⌊(x1 - x0) / lam⌋₊ = 2
      · exact Or.inr (Or.inl ⟨by omega, q1, by omega, by omega, by omega, by omega, by omega⟩)
      · by_cases q2 : ⌊(x2 - x1) / lam⌋₊ = 2
        · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, q2, by omega, by omega, by omega, by omega⟩))
        · by_cases q3 : ⌊(x3 - x2) / lam⌋₊ = 2
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, q3, by omega, by omega, by omega⟩)))
          · by_cases q4 : ⌊(x4 - x3) / lam⌋₊ = 2
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, q4, by omega, by omega⟩))))
            · by_cases q5 : ⌊(x5 - x4) / lam⌋₊ = 2
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, q5, by omega⟩)))))
              · by_cases q6 : ⌊(θ + Real.pi - x5) / lam⌋₊ = 2
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega, by omega, q6⟩))))))
                ·
                  exfalso; omega
  rw [s7fl2 hlam hg0, s7fl1 hlam hg0, s7fl2 hlam hg1, s7fl1 hlam hg1, s7fl2 hlam hg2, s7fl1 hlam hg2, s7fl2 hlam hg3, s7fl1 hlam hg3, s7fl2 hlam hg4, s7fl1 hlam hg4, s7fl2 hlam hg5, s7fl1 hlam hg5, s7fl2 hlam hg6, s7fl1 hlam hg6] at key
  simpa only [R2N4.RowSig1_8, and_assoc] using key

section EightCentreN4

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 8 → Plane₂} {v : Fin 8} {theta : Fin 7 → ℝ}
  (C : SatChart o e 4 lam c v theta)

include C

/-- Distinct non-anchor centres have distinct anchor directions. -/
theorem n8theta_injective : Function.Injective theta := by
  intro i j hij
  by_contra hne
  rcases up_or_up C hne with h | h
  · exact absurd hij (ne_of_lt (up_theta_lt C hne h))
  · exact absurd hij.symm (ne_of_lt (up_theta_lt C (Ne.symm hne) h))

/-- The seven non-anchor `theta`s are distinct. -/
theorem n8Tcard : (Finset.image theta Finset.univ).card = 7 := by
  classical
  rw [Finset.card_image_of_injective _ (n8theta_injective C),
    Finset.card_univ, Fintype.card_fin]

/-- Sorted `theta` values as a strict-mono enumeration. -/
noncomputable def n8T : Fin 7 → ℝ :=
  (Finset.image theta Finset.univ).orderEmbOfFin (n8Tcard C)

theorem n8T_strictMono : StrictMono (n8T C) := fun _ _ h =>
  ((Finset.image theta Finset.univ).orderEmbOfFin _).strictMono h

/-- Rank-to-index bijection: `n8σ C i` is the centre whose `theta` is
the `i`-th smallest. -/
noncomputable def n8σ : Fin 7 → Fin 7 := fun i =>
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n8Tcard C) i)).choose

theorem n8σ_spec (i : Fin 7) : theta (n8σ C i) = n8T C i :=
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n8Tcard C) i)).choose_spec.2

theorem n8σ_injective : Function.Injective (n8σ C) := by
  intro i j hij
  apply (n8T_strictMono C).injective
  rw [← n8σ_spec C i, ← n8σ_spec C j, hij]

theorem n8σ_bijective : Function.Bijective (n8σ C) :=
  Finite.injective_iff_bijective.mp (n8σ_injective C)

theorem n8σ_ne {i j : Fin 7} (h : i ≠ j) : n8σ C i ≠ n8σ C j :=
  fun hh => h (n8σ_injective C hh)

/-- A lower-`theta` centre is always `Up` of a higher one, at
`n8σ`-ranks. -/
theorem n8σ_up {i j : Fin 7} (hij : i < j) :
    Up o e c v (n8σ C i) (n8σ C j) := by
  have hlt : theta (n8σ C i) < theta (n8σ C j) := by
    rw [n8σ_spec C i, n8σ_spec C j]
    exact n8T_strictMono C hij
  exact up_of_theta_lt' C (n8σ_ne C hij.ne) hlt

/-- Corridor bounds in model coordinates. -/
theorem n8corridor {i j : Fin 7} (hij : i < j) :
    n8T C i + lam ≤
        dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j) ∧
      dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j) ≤
        Real.pi - lam + n8T C j := by
  have hcor := up_corridor C (n8σ_ne C hij.ne) (n8σ_up C hij)
  rwa [n8σ_spec C i, n8σ_spec C j] at hcor

/-- Triple `Up`-constraints in model coordinates. -/
theorem n8triple {i j k : Fin 7} (hij : i < j) (hjk : j < k) :
    (dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n8σ C j) (n8σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j) <
          dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C k) <
          dirRep o e (c ∘ v.succAbove) (n8σ C j) (n8σ C k)) ∨
      (dirRep o e (c ∘ v.succAbove) (n8σ C j) (n8σ C k) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j) ∧
        dirRep o e (c ∘ v.succAbove) (n8σ C j) (n8σ C k) <
          dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C k) <
          dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j)) := by
  have hl0 : 0 < lam := C.hlam
  have hneij : n8σ C i ≠ n8σ C j := n8σ_ne C hij.ne
  have hnejk : n8σ C j ≠ n8σ C k := n8σ_ne C hjk.ne
  have hneik : n8σ C i ≠ n8σ C k := n8σ_ne C (hij.trans hjk).ne
  have hupij := n8σ_up C hij
  have hupjk := n8σ_up C hjk
  obtain ⟨-, hbetween⟩ := up_trans C hneij hnejk hneik hupij hupjk
  have hcap := up_cap C hneij hnejk hneik hupij hupjk
  rcases le_or_gt 0 (dirRep o e (c ∘ v.succAbove) (n8σ C j) (n8σ C k) -
    dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j)) with hs | hs
  · rw [abs_of_nonneg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, h1, h2⟩
    · exfalso; linarith
  · rw [abs_of_neg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; linarith
    · exact Or.inr ⟨by linarith, h1, h2⟩

/-- The scalar `n = 4` model of the eight-centre configuration. -/
noncomputable def n8model : R2N4.N8Model where
  lam := lam
  p := Real.pi
  hlam := C.hlam
  hp := by
    have h1 := C.hnl
    have h2 := C.hπ
    push_cast at h1 h2
    constructor <;> linarith
  t := n8T C
  ht := n8T_strictMono C
  ht0 := by
    have h := (C.htheta (n8σ C 0)).1.1
    rwa [n8σ_spec C 0] at h
  ht6 := by
    have h := (C.htheta (n8σ C 6)).1.2
    rw [n8σ_spec C 6] at h
    push_cast at h ⊢
    linarith
  d := fun i j => dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j)
  hcor := fun _ _ h => n8corridor C h
  htr := fun _ _ _ h1 h2 => n8triple C h1 h2

theorem n8model_lam : (n8model C).lam = lam := rfl
theorem n8model_p : (n8model C).p = Real.pi := rfl
theorem n8model_t (i : Fin 7) : (n8model C).t i = n8T C i := rfl
theorem n8model_d (i j : Fin 7) :
    (n8model C).d i j =
      dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j) := rfl

/-- Rank identification: `n8σ C r = u` iff the `r`-th sorted `theta`
value is `theta u`. -/
theorem n8σ_eq_iff (u r : Fin 7) :
    n8σ C r = u ↔ n8T C r = theta u := by
  constructor
  · intro h; rw [← n8σ_spec C r, h]
  · intro h
    exact n8theta_injective C ((n8σ_spec C r).trans h)

/-- Rank via bisection: if every smaller rank lies strictly below
`theta u` and `n8T C r` does not, then `n8T C r = theta u`. -/
theorem n8T_eq_of_bounds (u : Fin 7) (r : Fin 7)
    (hlo : ∀ s : Fin 7, s < r → n8T C s < theta u)
    (hhi : theta u ≤ n8T C r) :
    n8T C r = theta u := by
  obtain ⟨r', hr'⟩ : ∃ r' : Fin 7, n8T C r' = theta u := by
    have hmem : theta u ∈ Set.range
        ⇑((Finset.image theta Finset.univ).orderEmbOfFin
          (n8Tcard C)) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
    exact hmem
  rcases lt_trichotomy r' r with hlt | heq | hgt
  · exact absurd (hlo r' hlt) (by rw [hr']; exact lt_irrefl _)
  · exact heq ▸ hr'
  · have h2 := n8T_strictMono C hgt
    rw [hr'] at h2
    linarith

/-- Chord symmetry in the model. -/
theorem n8d_comm (i j : Fin 7) (h : i ≠ j) :
    (n8model C).d i j = (n8model C).d j i := by
  have h' : n8σ C i ≠ n8σ C j := n8σ_ne C h
  exact phi_comm C h'

/-- Common core of `n8_row_exists`: the sorted six-chord list of the
row at chart index `u = n8σ C r`, with ordering and `List.Perm` onto
the model chords.  The score is returned for signature dispatch. -/
theorem n8_row_core {r u : Fin 7} (hu : n8σ C r = u)
    (hd : rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 2 ∨
      rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 3) :
    ∃ x0 x1 x2 x3 x4 x5 : ℝ,
      (n8T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧
        x4 ≤ x5 ∧ x5 ≤ n8T C r + Real.pi) ∧
      linearGapScore lam (n8T C r) (n8T C r + Real.pi)
          [x0, x1, x2, x3, x4, x5] = 4 - rowDefect 4 lam
            (directionRow o e c (v.succAbove u)) ∧
      List.Perm [x0, x1, x2, x3, x4, x5]
        (((List.finRange 7).erase r).map fun j =>
          (n8model C).d r j) := by
  classical
  have hTu : n8T C r = theta u := (n8σ_eq_iff C u r).mp hu
  have hlen : (directionRow o e (c ∘ v.succAbove) u).length = 6 := by
    have h := directionRow_length o e (c ∘ v.succAbove) u
    omega
  obtain ⟨x0, x1, x2, x3, x4, x5, hrest⟩ := length_eq_six hlen
  have hsort := directionRow_sorted o e (c ∘ v.succAbove) u
  rw [hrest] at hsort
  obtain ⟨h01', hs1⟩ := List.sortedLE_cons.mp hsort
  obtain ⟨h12', hs2⟩ := List.sortedLE_cons.mp hs1
  obtain ⟨h23', hs3⟩ := List.sortedLE_cons.mp hs2
  obtain ⟨h34', hs4⟩ := List.sortedLE_cons.mp hs3
  obtain ⟨h45', -⟩ := List.sortedLE_cons.mp hs4
  have e01 : x0 ≤ x1 := h01' x1 (by simp)
  have e12 : x1 ≤ x2 := h12' x2 (by simp)
  have e23 : x2 ≤ x3 := h23' x3 (by simp)
  have e34 : x3 ≤ x4 := h34' x4 (by simp)
  have e45 : x4 ≤ x5 := h45' x5 (by simp)
  have hmem : ∀ x ∈ directionRow o e (c ∘ v.succAbove) u,
      lam ≤ x ∧ x < Real.pi := by
    intro x hx
    obtain ⟨j, hju, rfl⟩ := (mem_directionRow o e
      (c ∘ v.succAbove)).mp hx
    exact ⟨phi_ge_lam C (Ne.symm hju), (linRep_mem_Ico _).2⟩
  have hβ : Real.pi - 4 * lam < lam := by exact_mod_cast C.hβ
  have hx0ge : theta u ≤ x0 := by
    have hx := (hmem x0 (by rw [hrest]; simp)).1
    have hθ : theta u ≤ Real.pi - 4 * lam := by
      exact_mod_cast (C.htheta u).1.2
    linarith
  have hx5le : x5 ≤ theta u + Real.pi := by
    have hx := (hmem x5 (by rw [hrest]; simp)).2
    have hθ0 := (C.htheta u).1.1
    linarith
  have hlampi : lam < Real.pi := by
    have h1 := C.hnl; have h2 := C.hn3'; have h3 := C.hlam; nlinarith
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) =
        (theta i : Real.Angle) := by
    intro i
    refine ⟨?_, (C.htheta i).2⟩
    have h := (C.htheta i).1
    rw [Set.mem_Icc] at h ⊢
    have h2 : theta i ≤ Real.pi - 4 * lam := by exact_mod_cast h.2
    exact ⟨h.1, by linarith⟩
  have hscore := anchored_rowScore_eq_linear o e C.he c C.hleg.inj v
    C.hlam hlampi theta htheta' (fun a b hab => phi_ge_lam C hab) u
  have hcells := rowCells_directionRow_le_of_floor_eq o e c C.hlam
    (v.succAbove u) (by omega) C.hn
  have hsub := rowScore_eq_sub_defect lam C.hlam 4 _ hcells
  rw [hscore, hrest, ← hTu] at hsub
  refine ⟨x0, x1, x2, x3, x4, x5, ?_, hsub, ?_⟩
  · rw [hTu]
    exact ⟨hx0ge, e01, e12, e23, e34, e45, hx5le⟩
  have hp1 : List.Perm (directionRow o e (c ∘ v.succAbove) u)
      (((List.finRange 7).erase u).map
        (dirRep o e (c ∘ v.succAbove) u)) :=
    List.perm_insertionSort _ _
  rw [hrest] at hp1
  have hmap : List.Perm ((List.finRange 7).erase u)
      (((List.finRange 7).erase r).map (n8σ C)) := by
    apply List.Subperm.antisymm
    · apply List.Nodup.subperm ((List.nodup_finRange 7).erase u)
      intro x hx
      rw [(List.nodup_finRange 7).mem_erase_iff] at hx
      obtain ⟨j, hj⟩ := (n8σ_bijective C).surjective x
      refine List.mem_map.mpr ⟨j, ?_, hj⟩
      rw [(List.nodup_finRange 7).mem_erase_iff]
      exact ⟨fun hjr => hx.1 (by rw [← hj, hjr, hu]),
        List.mem_finRange _⟩
    · apply List.Nodup.subperm
        (((List.nodup_finRange 7).erase r).map (n8σ_injective C))
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨j, hje, rfl⟩ := hx
      rw [(List.nodup_finRange 7).mem_erase_iff] at hje ⊢
      exact ⟨fun hxu => hje.1 (n8σ_injective C (hxu.trans hu.symm)),
        List.mem_finRange _⟩
  have hp2 := hmap.map (dirRep o e (c ∘ v.succAbove) u)
  rw [List.map_map] at hp2
  refine hp1.trans (hp2.trans ?_)
  have hfeq : (dirRep o e (c ∘ v.succAbove) u ∘ n8σ C) =
      fun j => (n8model C).d r j := by
    funext j
    show dirRep o e (c ∘ v.succAbove) u (n8σ C j) =
      (n8model C).d r j
    rw [n8model_d C r j, hu]
  rw [hfeq]

/-- A defect-`2` row at `n = 4` yields a `RowSig2_8` witness list. -/

end EightCentreN4
end Jsp404
