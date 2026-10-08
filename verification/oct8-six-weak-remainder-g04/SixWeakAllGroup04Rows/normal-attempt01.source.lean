import Jsp000404.SixWeakAllGroup04Data
import Jsp000404.SixDoubleAllGroup04Data
import Jsp000404.SixWeakOuterReplaySoundness
import Jsp000404.SixOuterWordCatalogComplete

/-! SOURCE_ONLY shared actual rows and literal-to-typed catalog bridges. -/
set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.SixWeakAllGroup04Rows
open SatScalarModel SixOuterReplay SixOuterReplaySoundness

def catalogIndices : Fin 10 → Fin 62 := ![51, 52, 53, 54, 55, 56, 57, 58, 59, 60]

theorem word_catalog_mask949 : SixWeakAllGroup04Data.Mask949.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (51 : Fin 62)) := by decide

theorem double_word_catalog_mask949 : SixDoubleAllGroup04Data.Mask949.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (51 : Fin 62)) := by
  exact word_catalog_mask949

#print axioms word_catalog_mask949
#print axioms double_word_catalog_mask949

theorem rows_actual_mask949 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup04Data.Mask949.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup04Data.Mask949.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup04Data.Mask949.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup04Data.Mask949.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup04Data.Mask949.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup04Data.Mask949.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup04Data.Mask949.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup04Data.Mask949.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup04Data.Mask949.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup04Data.Mask949.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup04Data.Mask949.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup04Data.Mask949.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup04Data.Mask949.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 4, M.d 0 2, M.d 0 1, M.d 0 3] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 4, M.d 1 2, M.d 1 0, M.d 1 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 4, M.d 2 1, M.d 2 0, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 4, M.d 3 0, M.d 3 1, M.d 3 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 3, M.d 4 2, M.d 4 1, M.d 4 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask949

theorem word_catalog_mask951 : SixWeakAllGroup04Data.Mask951.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (52 : Fin 62)) := by decide

theorem double_word_catalog_mask951 : SixDoubleAllGroup04Data.Mask951.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (52 : Fin 62)) := by
  exact word_catalog_mask951

#print axioms word_catalog_mask951
#print axioms double_word_catalog_mask951

theorem rows_actual_mask951 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup04Data.Mask951.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup04Data.Mask951.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup04Data.Mask951.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup04Data.Mask951.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup04Data.Mask951.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup04Data.Mask951.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup04Data.Mask951.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup04Data.Mask951.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup04Data.Mask951.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup04Data.Mask951.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup04Data.Mask951.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup04Data.Mask951.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup04Data.Mask951.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 4, M.d 0 2, M.d 0 3, M.d 0 1] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 4, M.d 1 2, M.d 1 3, M.d 1 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 4, M.d 2 1, M.d 2 0, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 4, M.d 3 1, M.d 3 0, M.d 3 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 3, M.d 4 2, M.d 4 1, M.d 4 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask951

theorem word_catalog_mask959 : SixWeakAllGroup04Data.Mask959.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (53 : Fin 62)) := by decide

theorem double_word_catalog_mask959 : SixDoubleAllGroup04Data.Mask959.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (53 : Fin 62)) := by
  exact word_catalog_mask959

#print axioms word_catalog_mask959
#print axioms double_word_catalog_mask959

theorem rows_actual_mask959 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup04Data.Mask959.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup04Data.Mask959.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup04Data.Mask959.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup04Data.Mask959.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup04Data.Mask959.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup04Data.Mask959.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup04Data.Mask959.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup04Data.Mask959.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup04Data.Mask959.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup04Data.Mask959.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup04Data.Mask959.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup04Data.Mask959.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup04Data.Mask959.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 4, M.d 0 3, M.d 0 2, M.d 0 1] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 4, M.d 1 2, M.d 1 3, M.d 1 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 4, M.d 2 1, M.d 2 3, M.d 2 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 4, M.d 3 1, M.d 3 2, M.d 3 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 3, M.d 4 2, M.d 4 1, M.d 4 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask959

theorem word_catalog_mask960 : SixWeakAllGroup04Data.Mask960.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (54 : Fin 62)) := by decide

theorem double_word_catalog_mask960 : SixDoubleAllGroup04Data.Mask960.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (54 : Fin 62)) := by
  exact word_catalog_mask960

#print axioms word_catalog_mask960
#print axioms double_word_catalog_mask960

theorem rows_actual_mask960 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup04Data.Mask960.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup04Data.Mask960.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup04Data.Mask960.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup04Data.Mask960.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup04Data.Mask960.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup04Data.Mask960.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup04Data.Mask960.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup04Data.Mask960.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup04Data.Mask960.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup04Data.Mask960.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup04Data.Mask960.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup04Data.Mask960.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup04Data.Mask960.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 0, M.d 1 4, M.d 1 3, M.d 1 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 0, M.d 2 4, M.d 2 3, M.d 2 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 0, M.d 3 4, M.d 3 2, M.d 3 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 0, M.d 4 3, M.d 4 2, M.d 4 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask960

theorem word_catalog_mask992 : SixWeakAllGroup04Data.Mask992.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (55 : Fin 62)) := by decide

theorem double_word_catalog_mask992 : SixDoubleAllGroup04Data.Mask992.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (55 : Fin 62)) := by
  exact word_catalog_mask992

#print axioms word_catalog_mask992
#print axioms double_word_catalog_mask992

theorem rows_actual_mask992 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup04Data.Mask992.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup04Data.Mask992.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup04Data.Mask992.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup04Data.Mask992.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup04Data.Mask992.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup04Data.Mask992.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup04Data.Mask992.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup04Data.Mask992.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup04Data.Mask992.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup04Data.Mask992.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup04Data.Mask992.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup04Data.Mask992.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup04Data.Mask992.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 1, M.d 0 2, M.d 0 4, M.d 0 3] : List ℝ).Pairwise (· ≤ ·)
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
    · change ([M.d 2 0, M.d 2 4, M.d 2 3, M.d 2 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 4, M.d 3 0, M.d 3 2, M.d 3 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 3, M.d 4 0, M.d 4 2, M.d 4 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask992

theorem word_catalog_mask1008 : SixWeakAllGroup04Data.Mask1008.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (56 : Fin 62)) := by decide

theorem double_word_catalog_mask1008 : SixDoubleAllGroup04Data.Mask1008.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (56 : Fin 62)) := by
  exact word_catalog_mask1008

#print axioms word_catalog_mask1008
#print axioms double_word_catalog_mask1008

theorem rows_actual_mask1008 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup04Data.Mask1008.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup04Data.Mask1008.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup04Data.Mask1008.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1008.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1008.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1008.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1008.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1008.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1008.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1008.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1008.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1008.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1008.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 1, M.d 0 4, M.d 0 2, M.d 0 3] : List ℝ).Pairwise (· ≤ ·)
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
    · change ([M.d 2 4, M.d 2 0, M.d 2 3, M.d 2 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 4, M.d 3 0, M.d 3 2, M.d 3 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 3, M.d 4 2, M.d 4 0, M.d 4 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask1008

theorem word_catalog_mask1012 : SixWeakAllGroup04Data.Mask1012.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (57 : Fin 62)) := by decide

theorem double_word_catalog_mask1012 : SixDoubleAllGroup04Data.Mask1012.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (57 : Fin 62)) := by
  exact word_catalog_mask1012

#print axioms word_catalog_mask1012
#print axioms double_word_catalog_mask1012

theorem rows_actual_mask1012 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup04Data.Mask1012.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup04Data.Mask1012.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup04Data.Mask1012.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1012.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1012.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1012.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1012.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1012.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1012.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1012.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1012.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1012.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1012.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 4, M.d 0 1, M.d 0 2, M.d 0 3] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 4, M.d 1 0, M.d 1 3, M.d 1 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 4, M.d 2 0, M.d 2 3, M.d 2 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 4, M.d 3 0, M.d 3 2, M.d 3 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 3, M.d 4 2, M.d 4 1, M.d 4 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask1012

theorem word_catalog_mask1016 : SixWeakAllGroup04Data.Mask1016.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (58 : Fin 62)) := by decide

theorem double_word_catalog_mask1016 : SixDoubleAllGroup04Data.Mask1016.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (58 : Fin 62)) := by
  exact word_catalog_mask1016

#print axioms word_catalog_mask1016
#print axioms double_word_catalog_mask1016

theorem rows_actual_mask1016 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup04Data.Mask1016.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup04Data.Mask1016.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup04Data.Mask1016.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1016.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1016.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1016.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1016.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1016.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1016.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1016.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1016.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1016.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1016.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 1, M.d 0 4, M.d 0 3, M.d 0 2] : List ℝ).Pairwise (· ≤ ·)
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
    · change ([M.d 2 4, M.d 2 3, M.d 2 0, M.d 2 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 4, M.d 3 2, M.d 3 0, M.d 3 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 3, M.d 4 2, M.d 4 0, M.d 4 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask1016

theorem word_catalog_mask1020 : SixWeakAllGroup04Data.Mask1020.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (59 : Fin 62)) := by decide

theorem double_word_catalog_mask1020 : SixDoubleAllGroup04Data.Mask1020.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (59 : Fin 62)) := by
  exact word_catalog_mask1020

#print axioms word_catalog_mask1020
#print axioms double_word_catalog_mask1020

theorem rows_actual_mask1020 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup04Data.Mask1020.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup04Data.Mask1020.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup04Data.Mask1020.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1020.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1020.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1020.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1020.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1020.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1020.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1020.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1020.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1020.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1020.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 4, M.d 0 1, M.d 0 3, M.d 0 2] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 4, M.d 1 0, M.d 1 3, M.d 1 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 4, M.d 2 3, M.d 2 0, M.d 2 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 4, M.d 3 2, M.d 3 0, M.d 3 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 3, M.d 4 2, M.d 4 1, M.d 4 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask1020

theorem word_catalog_mask1022 : SixWeakAllGroup04Data.Mask1022.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (60 : Fin 62)) := by decide

theorem double_word_catalog_mask1022 : SixDoubleAllGroup04Data.Mask1022.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (60 : Fin 62)) := by
  exact word_catalog_mask1022

#print axioms word_catalog_mask1022
#print axioms double_word_catalog_mask1022

theorem rows_actual_mask1022 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup04Data.Mask1022.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup04Data.Mask1022.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup04Data.Mask1022.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1022.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1022.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1022.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1022.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1022.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1022.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1022.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1022.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1022.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup04Data.Mask1022.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 4, M.d 0 3, M.d 0 1, M.d 0 2] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 4, M.d 1 3, M.d 1 0, M.d 1 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 4, M.d 2 3, M.d 2 0, M.d 2 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 4, M.d 3 2, M.d 3 1, M.d 3 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 3, M.d 4 2, M.d 4 1, M.d 4 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask1022

end Jsp404.SixWeakAllGroup04Rows
