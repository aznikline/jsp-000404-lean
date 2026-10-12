/-!
# Pure `Nat` case splits for the eight-centre row signatures

The `key` disjunctions of `Jsp404.rowSig2_8_of_linearScore_two` (28 branches) and
`Jsp404.rowSig1_8_of_linearScore_one` (7 branches) in `Jsp000404.S8N8Core`, with the seven
gap floors abstracted to `a0 … a6 : Nat`.  Same tactic text as the original in-place proofs;
split out (core Lean only, no imports) so the omega trees elaborate without the geometry closure.
-/

namespace Jsp404.S8ScoreArithmetic

set_option maxHeartbeats 1200000 in
/-- `key` of `Jsp404.rowSig2_8_of_linearScore_two` over abstract floors. -/
theorem rowSig2_8_key {a0 a1 a2 a3 a4 a5 a6 : Nat}
    (hsum : ((a0 - 1) + (a1 - 1) + (a2 - 1) + (a3 - 1) + (a4 - 1) + (a5 - 1) + (a6 - 1)) = 2)
    (b0 : a0 ≤ 3) (b1 : a1 ≤ 3) (b2 : a2 ≤ 3) (b3 : a3 ≤ 3) (b4 : a4 ≤ 3) (b5 : a5 ≤ 3) (b6 : a6 ≤ 3) :
    (a0 = 3 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 = 3 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 = 3 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 = 3 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 = 3 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 = 3 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 = 3) ∨
      (a0 = 2 ∧ a1 = 2 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 = 2 ∧ a1 ≤ 1 ∧ a2 = 2 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 = 2 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 = 2 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 = 2 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 = 2 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 = 2 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 = 2 ∧ a6 ≤ 1) ∨
      (a0 = 2 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 = 2) ∨
      (a0 ≤ 1 ∧ a1 = 2 ∧ a2 = 2 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 = 2 ∧ a2 ≤ 1 ∧ a3 = 2 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 = 2 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 = 2 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 = 2 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 = 2 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 = 2 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 = 2) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 = 2 ∧ a3 = 2 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 = 2 ∧ a3 ≤ 1 ∧ a4 = 2 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 = 2 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 = 2 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 = 2 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 = 2) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 = 2 ∧ a4 = 2 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 = 2 ∧ a4 ≤ 1 ∧ a5 = 2 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 = 2 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 = 2) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 = 2 ∧ a5 = 2 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 = 2 ∧ a5 ≤ 1 ∧ a6 = 2) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 = 2 ∧ a6 = 2) := by
  by_cases q0 : a0 = 3
  · exact Or.inl ⟨q0, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · by_cases q1 : a1 = 3
    · exact Or.inr (Or.inl ⟨by omega, q1, by omega, by omega, by omega, by omega, by omega⟩)
    · by_cases q2 : a2 = 3
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, q2, by omega, by omega, by omega, by omega⟩))
      · by_cases q3 : a3 = 3
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, q3, by omega, by omega, by omega⟩)))
        · by_cases q4 : a4 = 3
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, q4, by omega, by omega⟩))))
          · by_cases q5 : a5 = 3
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, q5, by omega⟩)))))
            · by_cases q6 : a6 = 3
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, by omega, q6⟩))))))
              ·
                by_cases r0 : a0 = 2
                ·
                  by_cases s1 : a1 = 2
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, s1, by omega, by omega, by omega, by omega, by omega⟩)))))))
                  ·
                    by_cases s2 : a2 = 2
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, by omega, s2, by omega, by omega, by omega, by omega⟩))))))))
                    ·
                      by_cases s3 : a3 = 2
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, by omega, by omega, s3, by omega, by omega, by omega⟩)))))))))
                      ·
                        by_cases s4 : a4 = 2
                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, by omega, by omega, by omega, s4, by omega, by omega⟩))))))))))
                        ·
                          by_cases s5 : a5 = 2
                          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, by omega, by omega, by omega, by omega, s5, by omega⟩)))))))))))
                          ·
                            have s6 : a6 = 2 := by omega
                            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r0, by omega, by omega, by omega, by omega, by omega, s6⟩))))))))))))
                ·
                  by_cases r1 : a1 = 2
                  ·
                    by_cases s2 : a2 = 2
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, r1, s2, by omega, by omega, by omega, by omega⟩)))))))))))))
                    ·
                      by_cases s3 : a3 = 2
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, r1, by omega, s3, by omega, by omega, by omega⟩))))))))))))))
                      ·
                        by_cases s4 : a4 = 2
                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, r1, by omega, by omega, s4, by omega, by omega⟩)))))))))))))))
                        ·
                          by_cases s5 : a5 = 2
                          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, r1, by omega, by omega, by omega, s5, by omega⟩))))))))))))))))
                          ·
                            have s6 : a6 = 2 := by omega
                            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, r1, by omega, by omega, by omega, by omega, s6⟩)))))))))))))))))
                  ·
                    by_cases r2 : a2 = 2
                    ·
                      by_cases s3 : a3 = 2
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, r2, s3, by omega, by omega, by omega⟩))))))))))))))))))
                      ·
                        by_cases s4 : a4 = 2
                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, r2, by omega, s4, by omega, by omega⟩)))))))))))))))))))
                        ·
                          by_cases s5 : a5 = 2
                          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, r2, by omega, by omega, s5, by omega⟩))))))))))))))))))))
                          ·
                            have s6 : a6 = 2 := by omega
                            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, r2, by omega, by omega, by omega, s6⟩)))))))))))))))))))))
                    ·
                      by_cases r3 : a3 = 2
                      ·
                        by_cases s4 : a4 = 2
                        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, r3, s4, by omega, by omega⟩))))))))))))))))))))))
                        ·
                          by_cases s5 : a5 = 2
                          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, r3, by omega, s5, by omega⟩)))))))))))))))))))))))
                          ·
                            have s6 : a6 = 2 := by omega
                            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, r3, by omega, by omega, s6⟩))))))))))))))))))))))))
                      ·
                        by_cases r4 : a4 = 2
                        ·
                          by_cases s5 : a5 = 2
                          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, r4, s5, by omega⟩)))))))))))))))))))))))))
                          ·
                            have s6 : a6 = 2 := by omega
                            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, r4, by omega, s6⟩))))))))))))))))))))))))))
                        ·
                          have r5 : a5 = 2 := by omega
                          have s6 : a6 = 2 := by omega
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega, r5, s6⟩)))))))))))))))))))))))))))

set_option maxHeartbeats 1200000 in
/-- `key` of `Jsp404.rowSig1_8_of_linearScore_one` over abstract floors. -/
theorem rowSig1_8_key {a0 a1 a2 a3 a4 a5 a6 : Nat}
    (hsum : ((a0 - 1) + (a1 - 1) + (a2 - 1) + (a3 - 1) + (a4 - 1) + (a5 - 1) + (a6 - 1)) = 1)
    (b0 : a0 ≤ 2) (b1 : a1 ≤ 2) (b2 : a2 ≤ 2) (b3 : a3 ≤ 2) (b4 : a4 ≤ 2) (b5 : a5 ≤ 2) (b6 : a6 ≤ 2) :
    (a0 = 2 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 = 2 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 = 2 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 = 2 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 = 2 ∧ a5 ≤ 1 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 = 2 ∧ a6 ≤ 1) ∨
      (a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 = 2) := by
  by_cases q0 : a0 = 2
  · exact Or.inl ⟨q0, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · by_cases q1 : a1 = 2
    · exact Or.inr (Or.inl ⟨by omega, q1, by omega, by omega, by omega, by omega, by omega⟩)
    · by_cases q2 : a2 = 2
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, q2, by omega, by omega, by omega, by omega⟩))
      · by_cases q3 : a3 = 2
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, q3, by omega, by omega, by omega⟩)))
        · by_cases q4 : a4 = 2
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, q4, by omega, by omega⟩))))
          · by_cases q5 : a5 = 2
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, q5, by omega⟩)))))
            · by_cases q6 : a6 = 2
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega, by omega, by omega, q6⟩))))))
              ·
                exfalso; omega

end Jsp404.S8ScoreArithmetic
