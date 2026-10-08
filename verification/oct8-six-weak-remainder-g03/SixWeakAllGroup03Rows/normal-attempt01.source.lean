import Jsp000404.SixWeakAllGroup03Data
import Jsp000404.SixDoubleAllGroup03Data
import Jsp000404.SixWeakOuterReplaySoundness
import Jsp000404.SixOuterWordCatalogComplete

/-! SOURCE_ONLY shared actual rows and literal-to-typed catalog bridges. -/
set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.SixWeakAllGroup03Rows
open SatScalarModel SixOuterReplay SixOuterReplaySoundness

def catalogIndices : Fin 16 → Fin 62 := ![35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]

theorem word_catalog_mask551 : SixWeakAllGroup03Data.Mask551.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (35 : Fin 62)) := by decide

theorem double_word_catalog_mask551 : SixDoubleAllGroup03Data.Mask551.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (35 : Fin 62)) := by
  exact word_catalog_mask551

#print axioms word_catalog_mask551
#print axioms double_word_catalog_mask551

theorem rows_actual_mask551 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask551.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask551.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask551.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask551.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask551.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask551.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask551.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask551.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask551.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask551.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask551.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask551.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask551.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 2, M.d 0 4, M.d 0 3, M.d 0 1] : List ℝ).Pairwise (· ≤ ·)
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
    · change ([M.d 2 1, M.d 2 0, M.d 2 4, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 1, M.d 3 4, M.d 3 0, M.d 3 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 1, M.d 4 3, M.d 4 0, M.d 4 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask551

theorem word_catalog_mask567 : SixWeakAllGroup03Data.Mask567.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (36 : Fin 62)) := by decide

theorem double_word_catalog_mask567 : SixDoubleAllGroup03Data.Mask567.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (36 : Fin 62)) := by
  exact word_catalog_mask567

#print axioms word_catalog_mask567
#print axioms double_word_catalog_mask567

theorem rows_actual_mask567 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask567.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask567.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask567.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask567.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask567.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask567.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask567.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask567.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask567.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask567.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask567.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask567.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask567.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 2, M.d 1 3, M.d 1 4, M.d 1 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 4, M.d 2 0, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 1, M.d 3 4, M.d 3 0, M.d 3 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 1, M.d 4 3, M.d 4 2, M.d 4 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask567

theorem word_catalog_mask575 : SixWeakAllGroup03Data.Mask575.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (37 : Fin 62)) := by decide

theorem double_word_catalog_mask575 : SixDoubleAllGroup03Data.Mask575.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (37 : Fin 62)) := by
  exact word_catalog_mask575

#print axioms word_catalog_mask575
#print axioms double_word_catalog_mask575

theorem rows_actual_mask575 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask575.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask575.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask575.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask575.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask575.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask575.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask575.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask575.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask575.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask575.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask575.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask575.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask575.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 2 1, M.d 2 4, M.d 2 3, M.d 2 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 1, M.d 3 4, M.d 3 2, M.d 3 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 1, M.d 4 3, M.d 4 2, M.d 4 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask575

theorem word_catalog_mask768 : SixWeakAllGroup03Data.Mask768.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (38 : Fin 62)) := by decide

theorem double_word_catalog_mask768 : SixDoubleAllGroup03Data.Mask768.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (38 : Fin 62)) := by
  exact word_catalog_mask768

#print axioms word_catalog_mask768
#print axioms double_word_catalog_mask768

theorem rows_actual_mask768 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask768.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask768.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask768.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask768.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask768.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask768.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask768.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask768.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask768.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask768.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask768.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask768.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask768.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 0, M.d 1 2, M.d 1 4, M.d 1 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 0, M.d 2 1, M.d 2 4, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 0, M.d 3 4, M.d 3 1, M.d 3 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 0, M.d 4 3, M.d 4 1, M.d 4 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask768

theorem word_catalog_mask769 : SixWeakAllGroup03Data.Mask769.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (39 : Fin 62)) := by decide

theorem double_word_catalog_mask769 : SixDoubleAllGroup03Data.Mask769.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (39 : Fin 62)) := by
  exact word_catalog_mask769

#print axioms word_catalog_mask769
#print axioms double_word_catalog_mask769

theorem rows_actual_mask769 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask769.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask769.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask769.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask769.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask769.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask769.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask769.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask769.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask769.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask769.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask769.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask769.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask769.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 2, M.d 1 0, M.d 1 4, M.d 1 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 0, M.d 2 4, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 0, M.d 3 4, M.d 3 1, M.d 3 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon30, hcanon31, hcanon32]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 4 0, M.d 4 3, M.d 4 1, M.d 4 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask769

theorem word_catalog_mask800 : SixWeakAllGroup03Data.Mask800.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (40 : Fin 62)) := by decide

theorem double_word_catalog_mask800 : SixDoubleAllGroup03Data.Mask800.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (40 : Fin 62)) := by
  exact word_catalog_mask800

#print axioms word_catalog_mask800
#print axioms double_word_catalog_mask800

theorem rows_actual_mask800 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask800.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask800.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask800.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask800.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask800.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask800.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask800.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask800.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask800.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask800.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask800.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask800.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask800.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 0, M.d 1 2, M.d 1 4, M.d 1 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 0, M.d 2 1, M.d 2 4, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
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
    · change ([M.d 4 3, M.d 4 0, M.d 4 1, M.d 4 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask800

theorem word_catalog_mask801 : SixWeakAllGroup03Data.Mask801.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (41 : Fin 62)) := by decide

theorem double_word_catalog_mask801 : SixDoubleAllGroup03Data.Mask801.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (41 : Fin 62)) := by
  exact word_catalog_mask801

#print axioms word_catalog_mask801
#print axioms double_word_catalog_mask801

theorem rows_actual_mask801 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask801.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask801.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask801.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask801.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask801.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask801.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask801.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask801.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask801.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask801.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask801.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask801.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask801.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 2, M.d 0 1, M.d 0 4, M.d 0 3] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 2, M.d 1 0, M.d 1 4, M.d 1 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 0, M.d 2 4, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
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
    · change ([M.d 4 3, M.d 4 0, M.d 4 1, M.d 4 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask801

theorem word_catalog_mask805 : SixWeakAllGroup03Data.Mask805.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (42 : Fin 62)) := by decide

theorem double_word_catalog_mask805 : SixDoubleAllGroup03Data.Mask805.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (42 : Fin 62)) := by
  exact word_catalog_mask805

#print axioms word_catalog_mask805
#print axioms double_word_catalog_mask805

theorem rows_actual_mask805 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask805.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask805.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask805.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask805.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask805.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask805.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask805.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask805.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask805.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask805.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask805.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask805.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask805.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 2, M.d 0 4, M.d 0 1, M.d 0 3] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 2, M.d 1 4, M.d 1 0, M.d 1 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 0, M.d 2 4, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
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
    · change ([M.d 4 3, M.d 4 1, M.d 4 0, M.d 4 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask805

theorem word_catalog_mask807 : SixWeakAllGroup03Data.Mask807.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (43 : Fin 62)) := by decide

theorem double_word_catalog_mask807 : SixDoubleAllGroup03Data.Mask807.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (43 : Fin 62)) := by
  exact word_catalog_mask807

#print axioms word_catalog_mask807
#print axioms double_word_catalog_mask807

theorem rows_actual_mask807 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask807.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask807.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask807.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask807.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask807.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask807.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask807.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask807.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask807.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask807.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask807.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask807.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask807.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 0 2, M.d 0 4, M.d 0 3, M.d 0 1] : List ℝ).Pairwise (· ≤ ·)
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 1 2, M.d 1 4, M.d 1 3, M.d 1 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 0, M.d 2 4, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
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
    · change ([M.d 4 3, M.d 4 1, M.d 4 0, M.d 4 2] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask807

theorem word_catalog_mask821 : SixWeakAllGroup03Data.Mask821.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (44 : Fin 62)) := by decide

theorem double_word_catalog_mask821 : SixDoubleAllGroup03Data.Mask821.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (44 : Fin 62)) := by
  exact word_catalog_mask821

#print axioms word_catalog_mask821
#print axioms double_word_catalog_mask821

theorem rows_actual_mask821 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask821.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask821.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask821.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask821.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask821.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask821.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask821.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask821.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask821.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask821.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask821.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask821.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask821.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 2, M.d 1 4, M.d 1 0, M.d 1 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 4, M.d 2 0, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
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
    · change ([M.d 4 3, M.d 4 1, M.d 4 2, M.d 4 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask821

theorem word_catalog_mask823 : SixWeakAllGroup03Data.Mask823.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (45 : Fin 62)) := by decide

theorem double_word_catalog_mask823 : SixDoubleAllGroup03Data.Mask823.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (45 : Fin 62)) := by
  exact word_catalog_mask823

#print axioms word_catalog_mask823
#print axioms double_word_catalog_mask823

theorem rows_actual_mask823 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask823.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask823.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask823.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask823.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask823.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask823.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask823.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask823.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask823.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask823.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask823.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask823.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask823.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 2, M.d 1 4, M.d 1 3, M.d 1 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 4, M.d 2 0, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
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
    · change ([M.d 4 3, M.d 4 1, M.d 4 2, M.d 4 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask823

theorem word_catalog_mask831 : SixWeakAllGroup03Data.Mask831.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (46 : Fin 62)) := by decide

theorem double_word_catalog_mask831 : SixDoubleAllGroup03Data.Mask831.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (46 : Fin 62)) := by
  exact word_catalog_mask831

#print axioms word_catalog_mask831
#print axioms double_word_catalog_mask831

theorem rows_actual_mask831 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask831.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask831.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask831.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask831.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask831.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask831.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask831.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask831.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask831.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask831.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask831.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask831.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask831.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 2, M.d 1 4, M.d 1 3, M.d 1 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 1, M.d 2 4, M.d 2 3, M.d 2 0] : List ℝ).Pairwise (· ≤ ·)
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
    · change ([M.d 4 3, M.d 4 1, M.d 4 2, M.d 4 0] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask831

theorem word_catalog_mask896 : SixWeakAllGroup03Data.Mask896.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (47 : Fin 62)) := by decide

theorem double_word_catalog_mask896 : SixDoubleAllGroup03Data.Mask896.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (47 : Fin 62)) := by
  exact word_catalog_mask896

#print axioms word_catalog_mask896
#print axioms double_word_catalog_mask896

theorem rows_actual_mask896 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask896.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask896.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask896.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask896.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask896.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask896.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask896.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask896.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask896.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask896.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask896.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask896.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask896.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 0, M.d 1 4, M.d 1 2, M.d 1 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 0, M.d 2 4, M.d 2 1, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon20, hcanon21]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 3 0, M.d 3 4, M.d 3 1, M.d 3 2] : List ℝ).Pairwise (· ≤ ·)
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

#print axioms rows_actual_mask896

theorem word_catalog_mask928 : SixWeakAllGroup03Data.Mask928.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (48 : Fin 62)) := by decide

theorem double_word_catalog_mask928 : SixDoubleAllGroup03Data.Mask928.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (48 : Fin 62)) := by
  exact word_catalog_mask928

#print axioms word_catalog_mask928
#print axioms double_word_catalog_mask928

theorem rows_actual_mask928 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask928.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask928.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask928.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask928.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask928.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask928.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask928.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask928.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask928.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask928.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask928.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask928.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask928.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 0, M.d 1 4, M.d 1 2, M.d 1 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 0, M.d 2 4, M.d 2 1, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
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
    · change ([M.d 4 3, M.d 4 0, M.d 4 2, M.d 4 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask928

theorem word_catalog_mask944 : SixWeakAllGroup03Data.Mask944.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (49 : Fin 62)) := by decide

theorem double_word_catalog_mask944 : SixDoubleAllGroup03Data.Mask944.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (49 : Fin 62)) := by
  exact word_catalog_mask944

#print axioms word_catalog_mask944
#print axioms double_word_catalog_mask944

theorem rows_actual_mask944 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask944.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask944.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask944.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask944.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask944.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask944.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask944.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask944.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask944.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask944.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask944.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask944.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask944.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 0, M.d 1 4, M.d 1 2, M.d 1 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 4, M.d 2 0, M.d 2 1, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
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
    · change ([M.d 4 3, M.d 4 2, M.d 4 0, M.d 4 1] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon40, hcanon41, hcanon42, hcanon43]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]

#print axioms rows_actual_mask944

theorem word_catalog_mask948 : SixWeakAllGroup03Data.Mask948.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (50 : Fin 62)) := by decide

theorem double_word_catalog_mask948 : SixDoubleAllGroup03Data.Mask948.word =
    SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (50 : Fin 62)) := by
  exact word_catalog_mask948

#print axioms word_catalog_mask948
#print axioms double_word_catalog_mask948

theorem rows_actual_mask948 (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup03Data.Mask948.word) :
    ∀ i, (List.ofFn (SixWeakAllGroup03Data.Mask948.rows i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (SixWeakAllGroup03Data.Mask948.rows i k))).Pairwise (· ≤ ·) := by
  have htri012 := hword 0
  norm_num [WordSound, SixWeakAllGroup03Data.Mask948.word, triples, triangleLow, triangleHigh, value] at htri012
  have htri013 := hword 1
  norm_num [WordSound, SixWeakAllGroup03Data.Mask948.word, triples, triangleLow, triangleHigh, value] at htri013
  have htri014 := hword 2
  norm_num [WordSound, SixWeakAllGroup03Data.Mask948.word, triples, triangleLow, triangleHigh, value] at htri014
  have htri023 := hword 3
  norm_num [WordSound, SixWeakAllGroup03Data.Mask948.word, triples, triangleLow, triangleHigh, value] at htri023
  have htri024 := hword 4
  norm_num [WordSound, SixWeakAllGroup03Data.Mask948.word, triples, triangleLow, triangleHigh, value] at htri024
  have htri034 := hword 5
  norm_num [WordSound, SixWeakAllGroup03Data.Mask948.word, triples, triangleLow, triangleHigh, value] at htri034
  have htri123 := hword 6
  norm_num [WordSound, SixWeakAllGroup03Data.Mask948.word, triples, triangleLow, triangleHigh, value] at htri123
  have htri124 := hword 7
  norm_num [WordSound, SixWeakAllGroup03Data.Mask948.word, triples, triangleLow, triangleHigh, value] at htri124
  have htri134 := hword 8
  norm_num [WordSound, SixWeakAllGroup03Data.Mask948.word, triples, triangleLow, triangleHigh, value] at htri134
  have htri234 := hword 9
  norm_num [WordSound, SixWeakAllGroup03Data.Mask948.word, triples, triangleLow, triangleHigh, value] at htri234
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
    · change ([M.d 1 4, M.d 1 0, M.d 1 2, M.d 1 3] : List ℝ).Pairwise (· ≤ ·)
      simp only [hcanon10]
      simp [List.pairwise_cons]
      all_goals
        repeat' apply And.intro
        all_goals linarith [htri012, htri013, htri014, htri023, htri024, htri034, htri123, htri124, htri134, htri234]
  · constructor
    · decide
    · change ([M.d 2 4, M.d 2 0, M.d 2 1, M.d 2 3] : List ℝ).Pairwise (· ≤ ·)
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

#print axioms rows_actual_mask948

end Jsp404.SixWeakAllGroup03Rows
