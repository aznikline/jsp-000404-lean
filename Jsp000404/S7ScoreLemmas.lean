import Jsp000404.S7Defs
import Jsp000404.IntervalPacking
import Jsp000404.Deletion

namespace Jsp404


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
theorem rowSig2_7_of_linearScore_two {lam θ : ℝ} (hlam : 0 < lam)
    {x0 x1 x2 x3 x4 : ℝ}
    (hord : θ ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ θ + Real.pi)
    (hsc : linearGapScore lam θ (θ + Real.pi) [x0, x1, x2, x3, x4] = 2) :
    R2N4.RowSig2_7 lam Real.pi θ x0 x1 x2 x3 x4 := by
  have hg0 : 0 ≤ (x0 - θ) := by linarith [hord.1]
  have hg1 : 0 ≤ (x1 - x0) := by linarith [hord.2.1]
  have hg2 : 0 ≤ (x2 - x1) := by linarith [hord.2.2.1]
  have hg3 : 0 ≤ (x3 - x2) := by linarith [hord.2.2.2.1]
  have hg4 : 0 ≤ (x4 - x3) := by linarith [hord.2.2.2.2.1]
  have hg5 : 0 ≤ (θ + Real.pi - x4) := by linarith [hord.2.2.2.2.2]
  have hsum : ((⌊(x0 - θ) / lam⌋₊ - 1) + (⌊(x1 - x0) / lam⌋₊ - 1) + (⌊(x2 - x1) / lam⌋₊ - 1) + (⌊(x3 - x2) / lam⌋₊ - 1) + (⌊(x4 - x3) / lam⌋₊ - 1) + (⌊(θ + Real.pi - x4) / lam⌋₊ - 1)) = 2 := by
    have h := hsc
    simp only [linearGapScore, gapScore] at h
    omega
  have b0 : ⌊(x0 - θ) / lam⌋₊ ≤ 3 := by omega
  have b1 : ⌊(x1 - x0) / lam⌋₊ ≤ 3 := by omega
  have b2 : ⌊(x2 - x1) / lam⌋₊ ≤ 3 := by omega
  have b3 : ⌊(x3 - x2) / lam⌋₊ ≤ 3 := by omega
  have b4 : ⌊(x4 - x3) / lam⌋₊ ≤ 3 := by omega
  have b5 : ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 3 := by omega
  have key :
      (⌊(x0 - θ) / lam⌋₊ = 3 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 3 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ = 3 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 3 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ = 3 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ = 3) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ = 2 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧ ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ = 2 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ = 2 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧ ⌊(x4 - x3) / lam⌋₊ = 2 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ = 2 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ = 2) := by
    by_cases q0 : ⌊(x0 - θ) / lam⌋₊ = 3
    · exact Or.inl ⟨q0, by omega, by omega, by omega, by omega, by omega⟩
    · by_cases q1 : ⌊(x1 - x0) / lam⌋₊ = 3
      · exact Or.inr (Or.inl ⟨by omega, q1, by omega, by omega, by omega, by omega⟩)
      · by_cases q2 : ⌊(x2 - x1) / lam⌋₊ = 3
        · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, q2, by omega, by omega, by omega⟩))
        · by_cases q3 : ⌊(x3 - x2) / lam⌋₊ = 3
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, q3, by omega, by omega⟩)))
          · by_cases q4 : ⌊(x4 - x3) / lam⌋₊ = 3
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, q4, by omega⟩))))
            · by_cases q5 : ⌊(θ + Real.pi - x4) / lam⌋₊ = 3
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, q5⟩)))))
              ·
                by_cases r0 : ⌊(x0 - θ) / lam⌋₊ = 2
                ·
                  by_cases s1 : ⌊(x1 - x0) / lam⌋₊ = 2
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, s1, by omega, by omega, by omega, by omega⟩))))))
                  ·
                    by_cases s2 : ⌊(x2 - x1) / lam⌋₊ = 2
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, by omega, s2, by omega, by omega, by omega⟩)))))))
                    ·
                      by_cases s3 : ⌊(x3 - x2) / lam⌋₊ = 2
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, by omega, by omega, s3, by omega, by omega⟩))))))))
                      ·
                        by_cases s4 : ⌊(x4 - x3) / lam⌋₊ = 2
                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, by omega, by omega, by omega, s4, by omega⟩)))))))))
                        ·
                          have s5 : ⌊(θ + Real.pi - x4) / lam⌋₊ = 2 := by omega
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, by omega, by omega, by omega, by omega, s5⟩))))))))))
                ·
                  by_cases r1 : ⌊(x1 - x0) / lam⌋₊ = 2
                  ·
                    by_cases s2 : ⌊(x2 - x1) / lam⌋₊ = 2
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, r1, s2, by omega, by omega, by omega⟩)))))))))))
                    ·
                      by_cases s3 : ⌊(x3 - x2) / lam⌋₊ = 2
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, r1, by omega, s3, by omega, by omega⟩))))))))))))
                      ·
                        by_cases s4 : ⌊(x4 - x3) / lam⌋₊ = 2
                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, r1, by omega, by omega, s4, by omega⟩)))))))))))))
                        ·
                          have s5 : ⌊(θ + Real.pi - x4) / lam⌋₊ = 2 := by omega
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, r1, by omega, by omega, by omega, s5⟩))))))))))))))
                  ·
                    by_cases r2 : ⌊(x2 - x1) / lam⌋₊ = 2
                    ·
                      by_cases s3 : ⌊(x3 - x2) / lam⌋₊ = 2
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, r2, s3, by omega, by omega⟩)))))))))))))))
                      ·
                        by_cases s4 : ⌊(x4 - x3) / lam⌋₊ = 2
                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, r2, by omega, s4, by omega⟩))))))))))))))))
                        ·
                          have s5 : ⌊(θ + Real.pi - x4) / lam⌋₊ = 2 := by omega
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, r2, by omega, by omega, s5⟩)))))))))))))))))
                    ·
                      by_cases r3 : ⌊(x3 - x2) / lam⌋₊ = 2
                      ·
                        by_cases s4 : ⌊(x4 - x3) / lam⌋₊ = 2
                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, r3, s4, by omega⟩))))))))))))))))))
                        ·
                          have s5 : ⌊(θ + Real.pi - x4) / lam⌋₊ = 2 := by omega
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, r3, by omega, s5⟩)))))))))))))))))))
                      ·
                        have r4 : ⌊(x4 - x3) / lam⌋₊ = 2 := by omega
                        have s5 : ⌊(θ + Real.pi - x4) / lam⌋₊ = 2 := by omega
                        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, r4, s5⟩))))))))))))))))))))
  rw [s7fl3 hlam hg0, s7fl2 hlam hg0, s7fl1 hlam hg0, s7fl3 hlam hg1, s7fl2 hlam hg1, s7fl1 hlam hg1, s7fl3 hlam hg2, s7fl2 hlam hg2, s7fl1 hlam hg2, s7fl3 hlam hg3, s7fl2 hlam hg3, s7fl1 hlam hg3, s7fl3 hlam hg4, s7fl2 hlam hg4, s7fl1 hlam hg4, s7fl3 hlam hg5, s7fl2 hlam hg5, s7fl1 hlam hg5] at key
  simpa only [R2N4.RowSig2_7, and_assoc] using key

set_option maxHeartbeats 1200000 in
theorem rowSig1_7_of_linearScore_one {lam θ : ℝ} (hlam : 0 < lam)
    {x0 x1 x2 x3 x4 : ℝ}
    (hord : θ ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ θ + Real.pi)
    (hsc : linearGapScore lam θ (θ + Real.pi) [x0, x1, x2, x3, x4] = 1) :
    R2N4.RowSig1_7 lam Real.pi θ x0 x1 x2 x3 x4 := by
  have hg0 : 0 ≤ (x0 - θ) := by linarith [hord.1]
  have hg1 : 0 ≤ (x1 - x0) := by linarith [hord.2.1]
  have hg2 : 0 ≤ (x2 - x1) := by linarith [hord.2.2.1]
  have hg3 : 0 ≤ (x3 - x2) := by linarith [hord.2.2.2.1]
  have hg4 : 0 ≤ (x4 - x3) := by linarith [hord.2.2.2.2.1]
  have hg5 : 0 ≤ (θ + Real.pi - x4) := by linarith [hord.2.2.2.2.2]
  have hsum : ((⌊(x0 - θ) / lam⌋₊ - 1) + (⌊(x1 - x0) / lam⌋₊ - 1) + (⌊(x2 - x1) / lam⌋₊ - 1) + (⌊(x3 - x2) / lam⌋₊ - 1) + (⌊(x4 - x3) / lam⌋₊ - 1) + (⌊(θ + Real.pi - x4) / lam⌋₊ - 1)) = 1 := by
    have h := hsc
    simp only [linearGapScore, gapScore] at h
    omega
  have b0 : ⌊(x0 - θ) / lam⌋₊ ≤ 2 := by omega
  have b1 : ⌊(x1 - x0) / lam⌋₊ ≤ 2 := by omega
  have b2 : ⌊(x2 - x1) / lam⌋₊ ≤ 2 := by omega
  have b3 : ⌊(x3 - x2) / lam⌋₊ ≤ 2 := by omega
  have b4 : ⌊(x4 - x3) / lam⌋₊ ≤ 2 := by omega
  have b5 : ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 2 := by omega
  have key :
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ = 2 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧ ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧ ⌊(x4 - x3) / lam⌋₊ ≤ 1 ∧ ⌊(θ + Real.pi - x4) / lam⌋₊ = 2) := by
    by_cases q0 : ⌊(x0 - θ) / lam⌋₊ = 2
    · exact Or.inl ⟨q0, by omega, by omega, by omega, by omega, by omega⟩
    · by_cases q1 : ⌊(x1 - x0) / lam⌋₊ = 2
      · exact Or.inr (Or.inl ⟨by omega, q1, by omega, by omega, by omega, by omega⟩)
      · by_cases q2 : ⌊(x2 - x1) / lam⌋₊ = 2
        · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, q2, by omega, by omega, by omega⟩))
        · by_cases q3 : ⌊(x3 - x2) / lam⌋₊ = 2
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, q3, by omega, by omega⟩)))
          · by_cases q4 : ⌊(x4 - x3) / lam⌋₊ = 2
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, q4, by omega⟩))))
            · by_cases q5 : ⌊(θ + Real.pi - x4) / lam⌋₊ = 2
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega, q5⟩)))))
              ·
                exfalso; omega
  rw [s7fl2 hlam hg0, s7fl1 hlam hg0, s7fl2 hlam hg1, s7fl1 hlam hg1, s7fl2 hlam hg2, s7fl1 hlam hg2, s7fl2 hlam hg3, s7fl1 hlam hg3, s7fl2 hlam hg4, s7fl1 hlam hg4, s7fl2 hlam hg5, s7fl1 hlam hg5] at key
  simpa only [R2N4.RowSig1_7, and_assoc] using key

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

end Jsp404
