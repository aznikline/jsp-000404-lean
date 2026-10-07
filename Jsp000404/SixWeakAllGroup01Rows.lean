import Jsp000404.SixWeakAllGroup01Data
import Jsp000404.SixDoubleAllGroup01Data
import Jsp000404.SixWeakOuterReplaySoundness
import Jsp000404.SixOuterWordCatalogComplete

/-! SOURCE_ONLY shared actual rows and literal-to-typed catalog bridges. -/
set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.SixWeakAllGroup01Rows
open SatScalarModel SixOuterReplay SixOuterReplaySoundness

def catalogIndices : Fin 16 → Fin 62 := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

theorem word_catalog_mask001 : SixWeakAllGroup01Data.Mask001.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (1 : Fin 62)) := by decide

theorem double_word_catalog_mask001 : SixDoubleAllGroup01Data.Mask001.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (1 : Fin 62)) := by
  exact word_catalog_mask001

#print axioms word_catalog_mask001
#print axioms double_word_catalog_mask001

theorem rows_actual_mask001 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask001.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask001.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask001.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask001.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask001.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask001.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask001.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask001.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask001.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask001.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask001.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask001.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask001.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 2, M.d 0 1, M.d 0 3, M.d 0 4] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 2, M.d 1 0, M.d 1 3, M.d 1 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 0, M.d 2 3, M.d 2 4] : List ℝ).Pairwise (· ≤ ·)
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

#print axioms rows_actual_mask001

theorem word_catalog_mask003 : SixWeakAllGroup01Data.Mask003.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (2 : Fin 62)) := by decide

theorem double_word_catalog_mask003 : SixDoubleAllGroup01Data.Mask003.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (2 : Fin 62)) := by
  exact word_catalog_mask003

#print axioms word_catalog_mask003
#print axioms double_word_catalog_mask003

theorem rows_actual_mask003 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask003.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask003.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask003.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask003.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask003.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask003.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask003.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask003.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask003.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask003.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask003.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask003.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask003.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 2, M.d 0 3, M.d 0 1, M.d 0 4] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 2, M.d 1 3, M.d 1 0, M.d 1 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 0, M.d 2 3, M.d 2 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 1, M.d 3 0, M.d 3 2, M.d 3 4] : List ℝ).Pairwise (· ≤ ·)
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

#print axioms rows_actual_mask003

theorem word_catalog_mask007 : SixWeakAllGroup01Data.Mask007.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (3 : Fin 62)) := by decide

theorem double_word_catalog_mask007 : SixDoubleAllGroup01Data.Mask007.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (3 : Fin 62)) := by
  exact word_catalog_mask007

#print axioms word_catalog_mask007
#print axioms double_word_catalog_mask007

theorem rows_actual_mask007 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask007.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask007.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask007.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask007.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask007.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask007.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask007.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask007.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask007.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask007.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask007.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask007.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask007.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 2, M.d 0 3, M.d 0 4, M.d 0 1] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 2, M.d 1 3, M.d 1 4, M.d 1 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 0, M.d 2 3, M.d 2 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 1, M.d 3 0, M.d 3 2, M.d 3 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 1, M.d 4 0, M.d 4 2, M.d 4 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask007

theorem word_catalog_mask011 : SixWeakAllGroup01Data.Mask011.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (4 : Fin 62)) := by decide

theorem double_word_catalog_mask011 : SixDoubleAllGroup01Data.Mask011.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (4 : Fin 62)) := by
  exact word_catalog_mask011

#print axioms word_catalog_mask011
#print axioms double_word_catalog_mask011

theorem rows_actual_mask011 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask011.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask011.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask011.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask011.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask011.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask011.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask011.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask011.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask011.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask011.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask011.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask011.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask011.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 3, M.d 0 2, M.d 0 1, M.d 0 4] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 2, M.d 1 3, M.d 1 0, M.d 1 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 3, M.d 2 0, M.d 2 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 1, M.d 3 2, M.d 3 0, M.d 3 4] : List ℝ).Pairwise (· ≤ ·)
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

#print axioms rows_actual_mask011

theorem word_catalog_mask015 : SixWeakAllGroup01Data.Mask015.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (5 : Fin 62)) := by decide

theorem double_word_catalog_mask015 : SixDoubleAllGroup01Data.Mask015.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (5 : Fin 62)) := by
  exact word_catalog_mask015

#print axioms word_catalog_mask015
#print axioms double_word_catalog_mask015

theorem rows_actual_mask015 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask015.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask015.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask015.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask015.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask015.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask015.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask015.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask015.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask015.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask015.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask015.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask015.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask015.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 3, M.d 0 2, M.d 0 4, M.d 0 1] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 2, M.d 1 3, M.d 1 4, M.d 1 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 3, M.d 2 0, M.d 2 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 1, M.d 3 2, M.d 3 0, M.d 3 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 1, M.d 4 0, M.d 4 2, M.d 4 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask015

theorem word_catalog_mask031 : SixWeakAllGroup01Data.Mask031.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (6 : Fin 62)) := by decide

theorem double_word_catalog_mask031 : SixDoubleAllGroup01Data.Mask031.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (6 : Fin 62)) := by
  exact word_catalog_mask031

#print axioms word_catalog_mask031
#print axioms double_word_catalog_mask031

theorem rows_actual_mask031 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask031.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask031.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask031.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask031.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask031.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask031.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask031.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask031.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask031.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask031.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask031.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask031.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask031.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 3, M.d 0 4, M.d 0 2, M.d 0 1] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 2, M.d 1 3, M.d 1 4, M.d 1 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 3, M.d 2 4, M.d 2 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 1, M.d 3 2, M.d 3 0, M.d 3 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 1, M.d 4 2, M.d 4 0, M.d 4 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask031

theorem word_catalog_mask063 : SixWeakAllGroup01Data.Mask063.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (7 : Fin 62)) := by decide

theorem double_word_catalog_mask063 : SixDoubleAllGroup01Data.Mask063.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (7 : Fin 62)) := by
  exact word_catalog_mask063

#print axioms word_catalog_mask063
#print axioms double_word_catalog_mask063

theorem rows_actual_mask063 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask063.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask063.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask063.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask063.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask063.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask063.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask063.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask063.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask063.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask063.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask063.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask063.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask063.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 2, M.d 1 3, M.d 1 4, M.d 1 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 3, M.d 2 4, M.d 2 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 1, M.d 3 2, M.d 3 4, M.d 3 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 1, M.d 4 2, M.d 4 3, M.d 4 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask063

theorem word_catalog_mask064 : SixWeakAllGroup01Data.Mask064.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (8 : Fin 62)) := by decide

theorem double_word_catalog_mask064 : SixDoubleAllGroup01Data.Mask064.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (8 : Fin 62)) := by
  exact word_catalog_mask064

#print axioms word_catalog_mask064
#print axioms double_word_catalog_mask064

theorem rows_actual_mask064 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask064.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask064.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask064.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask064.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask064.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask064.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask064.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask064.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask064.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask064.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask064.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask064.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask064.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 0, M.d 1 3, M.d 1 2, M.d 1 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 0, M.d 2 3, M.d 2 1, M.d 2 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 0, M.d 3 2, M.d 3 1, M.d 3 4] : List ℝ).Pairwise (· ≤ ·)
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

#print axioms rows_actual_mask064

theorem word_catalog_mask072 : SixWeakAllGroup01Data.Mask072.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (9 : Fin 62)) := by decide

theorem double_word_catalog_mask072 : SixDoubleAllGroup01Data.Mask072.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (9 : Fin 62)) := by
  exact word_catalog_mask072

#print axioms word_catalog_mask072
#print axioms double_word_catalog_mask072

theorem rows_actual_mask072 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask072.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask072.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask072.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask072.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask072.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask072.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask072.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask072.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask072.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask072.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask072.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask072.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask072.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 1, M.d 0 3, M.d 0 2, M.d 0 4] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 0, M.d 1 3, M.d 1 2, M.d 1 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 3, M.d 2 0, M.d 2 1, M.d 2 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 2, M.d 3 0, M.d 3 1, M.d 3 4] : List ℝ).Pairwise (· ≤ ·)
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

#print axioms rows_actual_mask072

theorem word_catalog_mask074 : SixWeakAllGroup01Data.Mask074.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (10 : Fin 62)) := by decide

theorem double_word_catalog_mask074 : SixDoubleAllGroup01Data.Mask074.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (10 : Fin 62)) := by
  exact word_catalog_mask074

#print axioms word_catalog_mask074
#print axioms double_word_catalog_mask074

theorem rows_actual_mask074 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask074.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask074.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask074.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask074.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask074.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask074.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask074.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask074.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask074.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask074.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask074.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask074.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask074.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 3, M.d 0 1, M.d 0 2, M.d 0 4] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 3, M.d 1 0, M.d 1 2, M.d 1 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 3, M.d 2 0, M.d 2 1, M.d 2 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 2, M.d 3 1, M.d 3 0, M.d 3 4] : List ℝ).Pairwise (· ≤ ·)
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

#print axioms rows_actual_mask074

theorem word_catalog_mask075 : SixWeakAllGroup01Data.Mask075.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (11 : Fin 62)) := by decide

theorem double_word_catalog_mask075 : SixDoubleAllGroup01Data.Mask075.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (11 : Fin 62)) := by
  exact word_catalog_mask075

#print axioms word_catalog_mask075
#print axioms double_word_catalog_mask075

theorem rows_actual_mask075 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask075.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask075.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask075.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask075.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask075.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask075.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask075.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask075.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask075.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask075.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask075.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask075.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask075.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 3, M.d 0 2, M.d 0 1, M.d 0 4] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 3, M.d 1 2, M.d 1 0, M.d 1 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 3, M.d 2 1, M.d 2 0, M.d 2 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 2, M.d 3 1, M.d 3 0, M.d 3 4] : List ℝ).Pairwise (· ≤ ·)
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

#print axioms rows_actual_mask075

theorem word_catalog_mask079 : SixWeakAllGroup01Data.Mask079.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (12 : Fin 62)) := by decide

theorem double_word_catalog_mask079 : SixDoubleAllGroup01Data.Mask079.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (12 : Fin 62)) := by
  exact word_catalog_mask079

#print axioms word_catalog_mask079
#print axioms double_word_catalog_mask079

theorem rows_actual_mask079 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask079.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask079.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask079.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask079.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask079.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask079.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask079.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask079.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask079.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask079.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask079.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask079.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask079.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 3, M.d 0 2, M.d 0 4, M.d 0 1] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 3, M.d 1 2, M.d 1 4, M.d 1 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 3, M.d 2 1, M.d 2 0, M.d 2 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 2, M.d 3 1, M.d 3 0, M.d 3 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 1, M.d 4 0, M.d 4 2, M.d 4 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask079

theorem word_catalog_mask095 : SixWeakAllGroup01Data.Mask095.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (13 : Fin 62)) := by decide

theorem double_word_catalog_mask095 : SixDoubleAllGroup01Data.Mask095.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (13 : Fin 62)) := by
  exact word_catalog_mask095

#print axioms word_catalog_mask095
#print axioms double_word_catalog_mask095

theorem rows_actual_mask095 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask095.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask095.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask095.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask095.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask095.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask095.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask095.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask095.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask095.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask095.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask095.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask095.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask095.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 3, M.d 0 4, M.d 0 2, M.d 0 1] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 3, M.d 1 2, M.d 1 4, M.d 1 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 3, M.d 2 1, M.d 2 4, M.d 2 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 2, M.d 3 1, M.d 3 0, M.d 3 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 1, M.d 4 2, M.d 4 0, M.d 4 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask095

theorem word_catalog_mask127 : SixWeakAllGroup01Data.Mask127.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (14 : Fin 62)) := by decide

theorem double_word_catalog_mask127 : SixDoubleAllGroup01Data.Mask127.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (14 : Fin 62)) := by
  exact word_catalog_mask127

#print axioms word_catalog_mask127
#print axioms double_word_catalog_mask127

theorem rows_actual_mask127 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask127.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask127.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask127.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask127.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask127.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask127.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask127.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask127.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask127.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask127.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask127.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask127.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask127.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 3, M.d 1 2, M.d 1 4, M.d 1 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 3, M.d 2 1, M.d 2 4, M.d 2 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 2, M.d 3 1, M.d 3 4, M.d 3 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 1, M.d 4 2, M.d 4 3, M.d 4 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask127

theorem word_catalog_mask192 : SixWeakAllGroup01Data.Mask192.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (15 : Fin 62)) := by decide

theorem double_word_catalog_mask192 : SixDoubleAllGroup01Data.Mask192.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (15 : Fin 62)) := by
  exact word_catalog_mask192

#print axioms word_catalog_mask192
#print axioms double_word_catalog_mask192

theorem rows_actual_mask192 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask192.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask192.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask192.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask192.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask192.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask192.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask192.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask192.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask192.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask192.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask192.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask192.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask192.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 0, M.d 1 3, M.d 1 4, M.d 1 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 0, M.d 2 3, M.d 2 4, M.d 2 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 0, M.d 3 2, M.d 3 1, M.d 3 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 0, M.d 4 2, M.d 4 1, M.d 4 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask192

theorem word_catalog_mask200 : SixWeakAllGroup01Data.Mask200.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (16 : Fin 62)) := by decide

theorem double_word_catalog_mask200 : SixDoubleAllGroup01Data.Mask200.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (16 : Fin 62)) := by
  exact word_catalog_mask200

#print axioms word_catalog_mask200
#print axioms double_word_catalog_mask200

theorem rows_actual_mask200 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup01Data.Mask200.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup01Data.Mask200.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup01Data.Mask200.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup01Data.Mask200.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup01Data.Mask200.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup01Data.Mask200.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup01Data.Mask200.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup01Data.Mask200.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup01Data.Mask200.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup01Data.Mask200.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup01Data.Mask200.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup01Data.Mask200.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup01Data.Mask200.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 1, M.d 0 3, M.d 0 2, M.d 0 4] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 0, M.d 1 3, M.d 1 4, M.d 1 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 3, M.d 2 0, M.d 2 4, M.d 2 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 2, M.d 3 0, M.d 3 1, M.d 3 4] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 0, M.d 4 2, M.d 4 1, M.d 4 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask200

end Jsp404.SixWeakAllGroup01Rows
