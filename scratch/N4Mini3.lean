import Jsp000404.N4Defs
import Jsp000404.N3Extraction

namespace Jsp404

open Classical
open scoped EuclideanSpace

set_option maxHeartbeats 800000 in
/-- Score `2` on a sorted four-chord anchored row is the `RowSig2`
signature: either one primitive gap lies in `[3λ, 4λ)` and the rest are
`< 2λ`, or two gaps lie in `[2λ, 3λ)` and the rest are `< 2λ`. -/
theorem rowSig2_of_linearScore_two {lam θ : ℝ} (hlam : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : θ ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ θ + Real.pi)
    (hsc : linearGapScore lam θ (θ + Real.pi) [x0, x1, x2, x3] = 2) :
    R2N4.RowSig2 lam Real.pi θ x0 x1 x2 x3 := by
  have hg0 : 0 ≤ x0 - θ := by linarith [hord.1]
  have hg1 : 0 ≤ x1 - x0 := by linarith [hord.2.1]
  have hg2 : 0 ≤ x2 - x1 := by linarith [hord.2.2.1]
  have hg3 : 0 ≤ x3 - x2 := by linarith [hord.2.2.2.1]
  have hg4 : 0 ≤ θ + Real.pi - x3 := by linarith [hord.2.2.2.2]
  have hsum : (⌊(x0 - θ) / lam⌋₊ - 1) + ((⌊(x1 - x0) / lam⌋₊ - 1) +
      ((⌊(x2 - x1) / lam⌋₊ - 1) + ((⌊(x3 - x2) / lam⌋₊ - 1) +
        (⌊(θ + Real.pi - x3) / lam⌋₊ - 1)))) = 2 := by
    have h := hsc
    simp only [linearGapScore, gapScore] at h
    omega
  have b0 : ⌊(x0 - θ) / lam⌋₊ ≤ 3 := by omega
  have b1 : ⌊(x1 - x0) / lam⌋₊ ≤ 3 := by omega
  have b2 : ⌊(x2 - x1) / lam⌋₊ ≤ 3 := by omega
  have b3 : ⌊(x3 - x2) / lam⌋₊ ≤ 3 := by omega
  have b4 : ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 3 := by omega
  have key :
      (⌊(x0 - θ) / lam⌋₊ = 3 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 3 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ = 3 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 3 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ = 3) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧
          ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ = 2) := by
    by_cases q0 : ⌊(x0 - θ) / lam⌋₊ = 3
    · exact Or.inl ⟨q0, by omega, by omega, by omega, by omega⟩
    · by_cases q1 : ⌊(x1 - x0) / lam⌋₊ = 3
      · exact Or.inr (Or.inl ⟨by omega, q1, by omega, by omega, by omega⟩)
      · by_cases q2 : ⌊(x2 - x1) / lam⌋₊ = 3
        · exact Or.inr (Or.inr (Or.inl
            ⟨by omega, by omega, q2, by omega, by omega⟩))
        · by_cases q3 : ⌊(x3 - x2) / lam⌋₊ = 3
          · exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨by omega, by omega, by omega, q3, by omega⟩)))
          · by_cases q4 : ⌊(θ + Real.pi - x3) / lam⌋₊ = 3
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨by omega, by omega, by omega, by omega, q4⟩))))
            · -- no gap has floor `3`: exactly two floors equal `2`.
              by_cases r0 : ⌊(x0 - θ) / lam⌋₊ = 2
              · by_cases r1 : ⌊(x1 - x0) / lam⌋₊ = 2
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨r0, r1, by omega, by omega, by omega⟩)))))
                · by_cases r2 : ⌊(x2 - x1) / lam⌋₊ = 2
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inl ⟨r0, by omega, r2, by omega, by omega⟩))))))
                  · by_cases r3 : ⌊(x3 - x2) / lam⌋₊ = 2
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inl
                          ⟨r0, by omega, by omega, r3, by omega⟩)))))))
                    · have r4 : ⌊(θ + Real.pi - x3) / lam⌋₊ = 2 := by omega
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inl
                          ⟨r0, by omega, by omega, by omega, r4⟩))))))))
              · by_cases s1 : ⌊(x1 - x0) / lam⌋₊ = 2
                · by_cases s2 : ⌊(x2 - x1) / lam⌋₊ = 2
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inl
                        ⟨by omega, s1, s2, by omega, by omega⟩)))))))))
                  · by_cases s3 : ⌊(x3 - x2) / lam⌋₊ = 2
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                          ⟨by omega, s1, by omega, s3, by omega⟩))))))))))
                    · have s4 : ⌊(θ + Real.pi - x3) / lam⌋₊ = 2 := by omega
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                          ⟨by omega, s1, by omega, by omega, s4⟩)))))))))))
                · by_cases t2 : ⌊(x2 - x1) / lam⌋₊ = 2
                  · by_cases t3 : ⌊(x3 - x2) / lam⌋₊ = 2
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                          (Or.inl
                            ⟨by omega, by omega, t2, t3, by omega⟩))))))))))))
                    · have t4 : ⌊(θ + Real.pi - x3) / lam⌋₊ = 2 := by omega
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                          (Or.inr (Or.inl
                            ⟨by omega, by omega, t2, by omega, t4⟩)))))))))))))
                  · have u3 : ⌊(x3 - x2) / lam⌋₊ = 2 := by omega
                    have u4 : ⌊(θ + Real.pi - x3) / lam⌋₊ = 2 := by omega
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr
                          ⟨by omega, by omega, by omega, u3, u4⟩))))))))))))))
  rw [floor_three_iff hlam hg0, floor_three_iff hlam hg1,
    floor_three_iff hlam hg2, floor_three_iff hlam hg3,
    floor_three_iff hlam hg4, floor_two_iff hlam hg0,
    floor_two_iff hlam hg1, floor_two_iff hlam hg2,
    floor_two_iff hlam hg3, floor_two_iff hlam hg4,
    floor_le_one_iff hlam hg0, floor_le_one_iff hlam hg1,
    floor_le_one_iff hlam hg2, floor_le_one_iff hlam hg3,
    floor_le_one_iff hlam hg4] at key
  rcases key with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    tauto

end Jsp404
