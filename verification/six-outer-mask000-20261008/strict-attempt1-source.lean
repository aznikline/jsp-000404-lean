import Jsp000404.SixOuterMask000Data
import Jsp000404.SixOuterReplaySoundness

/-! SOURCE_ONLY. A single actual direction-word branch. The caller provides
only the true ten triangle directions for this branch, never acyclicity,
a row ordering, floor profiles, or a cycle acceptance oracle. All-word
coverage remains a separate obligation; no Lean run is claimed. -/
set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.SixOuterMask000
open SatScalarModel SixOuterReplay SixOuterReplaySoundness

private theorem rows_actual (M : GenericModel 5 4)
    (hword : WordSound M SixOuterMask000Data.word) :
    ∀ i, (List.ofFn (SixOuterMask000Data.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixOuterMask000Data.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixOuterMask000Data.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixOuterMask000Data.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixOuterMask000Data.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixOuterMask000Data.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixOuterMask000Data.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixOuterMask000Data.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixOuterMask000Data.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixOuterMask000Data.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixOuterMask000Data.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixOuterMask000Data.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 1, M.d 0 2, M.d 0 3, M.d 0 4] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 0, M.d 1 2, M.d 1 3, M.d 1 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 0, M.d 2 1, M.d 2 3, M.d 2 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 0, M.d 3 1, M.d 3 2, M.d 3 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 0, M.d 4 1, M.d 4 2, M.d 4 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

/-- The n4 CORE75 is impossible in the actual all-forward triangle branch.
Rows0,2,4 have no defect restriction and there is no HIGH premise. -/
theorem mask000_impossible (M : GenericModel 5 4)
    (hword : WordSound M SixOuterMask000Data.word)
    (hdef1 : SatScalarModel.rowDefect M 1 = 2)
    (hdef3 : SatScalarModel.rowDefect M 3 = 3) : False := by
  exact leafCheck_sound M SixOuterMask000Data.word hword SixOuterMask000Data.rows
    (rows_actual M hword) hdef1 hdef3 SixOuterMask000Data.library SixOuterMask000Data.ids
    SixOuterMask000Data.point_checked

#print axioms mask000_impossible
end Jsp404.SixOuterMask000
