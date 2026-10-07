import Jsp000404.SixDoubleLowMask472Data
import Jsp000404.SixWeakOuterReplaySoundness

/-! SOURCE_ONLY one-real-word actual pilot. Complete original rows are
proved internally from the ten actual direction bits; no caller order,
gap profile, acyclicity or accepted certificate is assumed. -/
set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.SixDoubleLowMask472
open SatScalarModel SixOuterReplay SixOuterReplaySoundness

private theorem rows_actual (M : GenericModel 5 4)
    (hword : WordSound M SixDoubleLowMask472Data.word) :
    ∀ i, (List.ofFn (SixDoubleLowMask472Data.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixDoubleLowMask472Data.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixDoubleLowMask472Data.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixDoubleLowMask472Data.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixDoubleLowMask472Data.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixDoubleLowMask472Data.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixDoubleLowMask472Data.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixDoubleLowMask472Data.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixDoubleLowMask472Data.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixDoubleLowMask472Data.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixDoubleLowMask472Data.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixDoubleLowMask472Data.word, triples, triangleLow, triangleHigh, value] at htri234
  have hcanon10 : M.d 1 0 = M.d 0 1 := M.symm 1 0 (by decide)
  have hcanon20 : M.d 2 0 = M.d 0 2 := M.symm 2 0 (by decide)
  have hcanon21 : M.d 2 1 = M.d 1 2 := M.symm 2 1 (by decide)
  have hcanon30 : M.d 3 0 = M.d 0 3 := M.symm 3 0 (by decide)
  have hcanon31 : M.d 3 1 = M.d 1 3 := M.symm 3 1 (by decide)
  have hcanon32 : M.d 3 2 = M.d 2 3 := M.symm 3 2 (by decide)
  have hcanon40 : M.d 4 0 = M.d 0 4 := M.symm 4 0 (by decide)
  have hcanon41 : M.d 4 1 = M.d 1 4 := M.symm 4 1 (by decide)
  have hcanon42 : M.d 4 2 = M.d 2 4 := M.symm 4 2 (by decide)
  have hcanon43 : M.d 4 3 = M.d 3 4 := M.symm 4 3 (by decide)
  intro i
  fin_cases i
  · constructor
    · decide
    · change ([M.d 0 1, M.d 0 3, M.d 0 4, M.d 0 2] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 0, M.d 1 4, M.d 1 3, M.d 1 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 3, M.d 2 4, M.d 2 0, M.d 2 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 2, M.d 3 0, M.d 3 4, M.d 3 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 2, M.d 4 0, M.d 4 3, M.d 4 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

theorem double225_mask472_impossible (M : GenericModel 5 4)
    (hword : WordSound M SixDoubleLowMask472Data.word)
    (hdef0 : SatScalarModel.rowDefect M 0 ≤ 2)
    (hdef2 : SatScalarModel.rowDefect M 2 ≤ 2)
    : False := by
  exact SixWeakOuterReplaySoundness.leafCheckB_sound M SixDoubleLowMask472Data.word hword SixDoubleLowMask472Data.rows
    (rows_actual M hword) hdef0 hdef2 SixDoubleLowMask472Data.library SixDoubleLowMask472Data.ids SixDoubleLowMask472Data.point_checked

#print axioms double225_mask472_impossible
end Jsp404.SixDoubleLowMask472
