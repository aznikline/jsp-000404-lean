import Jsp000404.N4R2CriticalKernelPrimitives

/-! SOURCE-ONLY conditional fixed-direction probe. The direction
hypotheses are explicit internal-subcase premises; this is not the
public eight-point exclusion and does not cover all triangle Or arms. -/

set_option autoImplicit false
set_option pp.fullNames true
namespace Jsp404.N4R2CriticalKernel
open SatScalarModel StrongGapBudget

set_option maxHeartbeats 16000000 in
theorem fixed_word_low6_probe (M : GenericModel 7 4)
    (hdef2 : SatScalarModel.rowDefect M 2 = 4)
    (hdef4 : SatScalarModel.rowDefect M 4 = 4)
    (hdef5 : SatScalarModel.rowDefect M 5 = 4)
    (hdef6 : SatScalarModel.rowDefect M 6 = 2)
    (htri012 : M.d 0 1+1 ≤ M.d 1 2 ∧ M.d 0 1 < M.d 0 2 ∧ M.d 0 2 < M.d 1 2)
    (htri013 : M.d 0 1+1 ≤ M.d 1 3 ∧ M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (htri014 : M.d 0 1+1 ≤ M.d 1 4 ∧ M.d 0 1 < M.d 0 4 ∧ M.d 0 4 < M.d 1 4)
    (htri015 : M.d 0 1+1 ≤ M.d 1 5 ∧ M.d 0 1 < M.d 0 5 ∧ M.d 0 5 < M.d 1 5)
    (htri016 : M.d 0 1+1 ≤ M.d 1 6 ∧ M.d 0 1 < M.d 0 6 ∧ M.d 0 6 < M.d 1 6)
    (htri023 : M.d 0 2+1 ≤ M.d 2 3 ∧ M.d 0 2 < M.d 0 3 ∧ M.d 0 3 < M.d 2 3)
    (htri024 : M.d 0 2+1 ≤ M.d 2 4 ∧ M.d 0 2 < M.d 0 4 ∧ M.d 0 4 < M.d 2 4)
    (htri025 : M.d 0 2+1 ≤ M.d 2 5 ∧ M.d 0 2 < M.d 0 5 ∧ M.d 0 5 < M.d 2 5)
    (htri026 : M.d 0 2+1 ≤ M.d 2 6 ∧ M.d 0 2 < M.d 0 6 ∧ M.d 0 6 < M.d 2 6)
    (htri034 : M.d 0 3+1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (htri035 : M.d 0 3+1 ≤ M.d 3 5 ∧ M.d 0 3 < M.d 0 5 ∧ M.d 0 5 < M.d 3 5)
    (htri036 : M.d 0 3+1 ≤ M.d 3 6 ∧ M.d 0 3 < M.d 0 6 ∧ M.d 0 6 < M.d 3 6)
    (htri045 : M.d 0 4+1 ≤ M.d 4 5 ∧ M.d 0 4 < M.d 0 5 ∧ M.d 0 5 < M.d 4 5)
    (htri046 : M.d 0 4+1 ≤ M.d 4 6 ∧ M.d 0 4 < M.d 0 6 ∧ M.d 0 6 < M.d 4 6)
    (htri056 : M.d 0 5+1 ≤ M.d 5 6 ∧ M.d 0 5 < M.d 0 6 ∧ M.d 0 6 < M.d 5 6)
    (htri123 : M.d 2 3+1 ≤ M.d 1 2 ∧ M.d 2 3 < M.d 1 3 ∧ M.d 1 3 < M.d 1 2)
    (htri124 : M.d 1 2+1 ≤ M.d 2 4 ∧ M.d 1 2 < M.d 1 4 ∧ M.d 1 4 < M.d 2 4)
    (htri125 : M.d 2 5+1 ≤ M.d 1 2 ∧ M.d 2 5 < M.d 1 5 ∧ M.d 1 5 < M.d 1 2)
    (htri126 : M.d 1 2+1 ≤ M.d 2 6 ∧ M.d 1 2 < M.d 1 6 ∧ M.d 1 6 < M.d 2 6)
    (htri134 : M.d 1 3+1 ≤ M.d 3 4 ∧ M.d 1 3 < M.d 1 4 ∧ M.d 1 4 < M.d 3 4)
    (htri135 : M.d 1 3+1 ≤ M.d 3 5 ∧ M.d 1 3 < M.d 1 5 ∧ M.d 1 5 < M.d 3 5)
    (htri136 : M.d 1 3+1 ≤ M.d 3 6 ∧ M.d 1 3 < M.d 1 6 ∧ M.d 1 6 < M.d 3 6)
    (htri145 : M.d 4 5+1 ≤ M.d 1 4 ∧ M.d 4 5 < M.d 1 5 ∧ M.d 1 5 < M.d 1 4)
    (htri146 : M.d 4 6+1 ≤ M.d 1 4 ∧ M.d 4 6 < M.d 1 6 ∧ M.d 1 6 < M.d 1 4)
    (htri156 : M.d 1 5+1 ≤ M.d 5 6 ∧ M.d 1 5 < M.d 1 6 ∧ M.d 1 6 < M.d 5 6)
    (htri234 : M.d 2 3+1 ≤ M.d 3 4 ∧ M.d 2 3 < M.d 2 4 ∧ M.d 2 4 < M.d 3 4)
    (htri235 : M.d 2 3+1 ≤ M.d 3 5 ∧ M.d 2 3 < M.d 2 5 ∧ M.d 2 5 < M.d 3 5)
    (htri236 : M.d 2 3+1 ≤ M.d 3 6 ∧ M.d 2 3 < M.d 2 6 ∧ M.d 2 6 < M.d 3 6)
    (htri245 : M.d 4 5+1 ≤ M.d 2 4 ∧ M.d 4 5 < M.d 2 5 ∧ M.d 2 5 < M.d 2 4)
    (htri246 : M.d 4 6+1 ≤ M.d 2 4 ∧ M.d 4 6 < M.d 2 6 ∧ M.d 2 6 < M.d 2 4)
    (htri256 : M.d 2 5+1 ≤ M.d 5 6 ∧ M.d 2 5 < M.d 2 6 ∧ M.d 2 6 < M.d 5 6)
    (htri345 : M.d 4 5+1 ≤ M.d 3 4 ∧ M.d 4 5 < M.d 3 5 ∧ M.d 3 5 < M.d 3 4)
    (htri346 : M.d 4 6+1 ≤ M.d 3 4 ∧ M.d 4 6 < M.d 3 6 ∧ M.d 3 6 < M.d 3 4)
    (htri356 : M.d 3 5+1 ≤ M.d 5 6 ∧ M.d 3 5 < M.d 3 6 ∧ M.d 3 6 < M.d 5 6)
    (htri456 : M.d 4 5+1 ≤ M.d 5 6 ∧ M.d 4 5 < M.d 4 6 ∧ M.d 4 6 < M.d 5 6)
    : False := by
  have hdelta1 := M.hdelta.2
  obtain ⟨ht0a, ht0b⟩ := M.theta_bounds 0
  have ht01 := M.htheta (show (0 : Fin 7) < 1 from by decide)
  obtain ⟨ht1a, ht1b⟩ := M.theta_bounds 1
  have ht12 := M.htheta (show (1 : Fin 7) < 2 from by decide)
  obtain ⟨ht2a, ht2b⟩ := M.theta_bounds 2
  have ht23 := M.htheta (show (2 : Fin 7) < 3 from by decide)
  obtain ⟨ht3a, ht3b⟩ := M.theta_bounds 3
  have ht34 := M.htheta (show (3 : Fin 7) < 4 from by decide)
  obtain ⟨ht4a, ht4b⟩ := M.theta_bounds 4
  have ht45 := M.htheta (show (4 : Fin 7) < 5 from by decide)
  obtain ⟨ht5a, ht5b⟩ := M.theta_bounds 5
  have ht56 := M.htheta (show (5 : Fin 7) < 6 from by decide)
  obtain ⟨ht6a, ht6b⟩ := M.theta_bounds 6
  obtain ⟨hc01a, hc01b⟩ := M.corridor 0 1 (by decide)
  norm_num at hc01b
  obtain ⟨hc02a, hc02b⟩ := M.corridor 0 2 (by decide)
  norm_num at hc02b
  obtain ⟨hc03a, hc03b⟩ := M.corridor 0 3 (by decide)
  norm_num at hc03b
  obtain ⟨hc04a, hc04b⟩ := M.corridor 0 4 (by decide)
  norm_num at hc04b
  obtain ⟨hc05a, hc05b⟩ := M.corridor 0 5 (by decide)
  norm_num at hc05b
  obtain ⟨hc06a, hc06b⟩ := M.corridor 0 6 (by decide)
  norm_num at hc06b
  obtain ⟨hc12a, hc12b⟩ := M.corridor 1 2 (by decide)
  norm_num at hc12b
  obtain ⟨hc13a, hc13b⟩ := M.corridor 1 3 (by decide)
  norm_num at hc13b
  obtain ⟨hc14a, hc14b⟩ := M.corridor 1 4 (by decide)
  norm_num at hc14b
  obtain ⟨hc15a, hc15b⟩ := M.corridor 1 5 (by decide)
  norm_num at hc15b
  obtain ⟨hc16a, hc16b⟩ := M.corridor 1 6 (by decide)
  norm_num at hc16b
  obtain ⟨hc23a, hc23b⟩ := M.corridor 2 3 (by decide)
  norm_num at hc23b
  obtain ⟨hc24a, hc24b⟩ := M.corridor 2 4 (by decide)
  norm_num at hc24b
  obtain ⟨hc25a, hc25b⟩ := M.corridor 2 5 (by decide)
  norm_num at hc25b
  obtain ⟨hc26a, hc26b⟩ := M.corridor 2 6 (by decide)
  norm_num at hc26b
  obtain ⟨hc34a, hc34b⟩ := M.corridor 3 4 (by decide)
  norm_num at hc34b
  obtain ⟨hc35a, hc35b⟩ := M.corridor 3 5 (by decide)
  norm_num at hc35b
  obtain ⟨hc36a, hc36b⟩ := M.corridor 3 6 (by decide)
  norm_num at hc36b
  obtain ⟨hc45a, hc45b⟩ := M.corridor 4 5 (by decide)
  norm_num at hc45b
  obtain ⟨hc46a, hc46b⟩ := M.corridor 4 6 (by decide)
  norm_num at hc46b
  obtain ⟨hc56a, hc56b⟩ := M.corridor 5 6 (by decide)
  norm_num at hc56b
  obtain ⟨htr012a,htr012b,htr012c⟩ := htri012
  obtain ⟨htr013a,htr013b,htr013c⟩ := htri013
  obtain ⟨htr014a,htr014b,htr014c⟩ := htri014
  obtain ⟨htr015a,htr015b,htr015c⟩ := htri015
  obtain ⟨htr016a,htr016b,htr016c⟩ := htri016
  obtain ⟨htr023a,htr023b,htr023c⟩ := htri023
  obtain ⟨htr024a,htr024b,htr024c⟩ := htri024
  obtain ⟨htr025a,htr025b,htr025c⟩ := htri025
  obtain ⟨htr026a,htr026b,htr026c⟩ := htri026
  obtain ⟨htr034a,htr034b,htr034c⟩ := htri034
  obtain ⟨htr035a,htr035b,htr035c⟩ := htri035
  obtain ⟨htr036a,htr036b,htr036c⟩ := htri036
  obtain ⟨htr045a,htr045b,htr045c⟩ := htri045
  obtain ⟨htr046a,htr046b,htr046c⟩ := htri046
  obtain ⟨htr056a,htr056b,htr056c⟩ := htri056
  obtain ⟨htr123a,htr123b,htr123c⟩ := htri123
  obtain ⟨htr124a,htr124b,htr124c⟩ := htri124
  obtain ⟨htr125a,htr125b,htr125c⟩ := htri125
  obtain ⟨htr126a,htr126b,htr126c⟩ := htri126
  obtain ⟨htr134a,htr134b,htr134c⟩ := htri134
  obtain ⟨htr135a,htr135b,htr135c⟩ := htri135
  obtain ⟨htr136a,htr136b,htr136c⟩ := htri136
  obtain ⟨htr145a,htr145b,htr145c⟩ := htri145
  obtain ⟨htr146a,htr146b,htr146c⟩ := htri146
  obtain ⟨htr156a,htr156b,htr156c⟩ := htri156
  obtain ⟨htr234a,htr234b,htr234c⟩ := htri234
  obtain ⟨htr235a,htr235b,htr235c⟩ := htri235
  obtain ⟨htr236a,htr236b,htr236c⟩ := htri236
  obtain ⟨htr245a,htr245b,htr245c⟩ := htri245
  obtain ⟨htr246a,htr246b,htr246c⟩ := htri246
  obtain ⟨htr256a,htr256b,htr256c⟩ := htri256
  obtain ⟨htr345a,htr345b,htr345c⟩ := htri345
  obtain ⟨htr346a,htr346b,htr346c⟩ := htri346
  obtain ⟨htr356a,htr356b,htr356c⟩ := htri356
  obtain ⟨htr456a,htr456b,htr456c⟩ := htri456
  have hsort2 : ([M.d 0 2, M.d 2 3, M.d 2 5, M.d 1 2, M.d 2 6, M.d 2 4] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp2 := M.row_perm 2
  have hcanon20 : M.d 2 0 = M.d 0 2 := M.symm 2 0 (by decide)
  have hcanon21 : M.d 2 1 = M.d 1 2 := M.symm 2 1 (by decide)
  have he2 : (((List.finRange 7).erase (2 : Fin 7)).map (M.d 2)) = [M.d 0 2, M.d 1 2, M.d 2 3, M.d 2 4, M.d 2 5, M.d 2 6] := by
    norm_num [List.finRange,List.ofFn_succ,hcanon20, hcanon21]
  rw [he2] at hp2
  have hperm2 := hp2.trans ((((((List.Perm.swap (M.d 2 3) (M.d 1 2) [M.d 2 4, M.d 2 5, M.d 2 6]).cons (M.d 0 2)).trans ((((List.Perm.swap (M.d 2 5) (M.d 2 4) [M.d 2 6]).cons (M.d 1 2)).cons (M.d 2 3)).cons (M.d 0 2))).trans (((List.Perm.swap (M.d 2 5) (M.d 1 2) [M.d 2 4, M.d 2 6]).cons (M.d 2 3)).cons (M.d 0 2))).trans (((((List.Perm.swap (M.d 2 6) (M.d 2 4) []).cons (M.d 1 2)).cons (M.d 2 5)).cons (M.d 2 3)).cons (M.d 0 2))))
  have hrow2 : M.rowxs 2 = [M.d 0 2, M.d 2 3, M.d 2 5, M.d 1 2, M.d 2 6, M.d 2 4] := hperm2.eq_of_pairwise' (M.row_sorted 2) hsort2
  have hsort4 : ([M.d 0 4, M.d 4 5, M.d 4 6, M.d 1 4, M.d 2 4, M.d 3 4] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp4 := M.row_perm 4
  have hcanon40 : M.d 4 0 = M.d 0 4 := M.symm 4 0 (by decide)
  have hcanon41 : M.d 4 1 = M.d 1 4 := M.symm 4 1 (by decide)
  have hcanon42 : M.d 4 2 = M.d 2 4 := M.symm 4 2 (by decide)
  have hcanon43 : M.d 4 3 = M.d 3 4 := M.symm 4 3 (by decide)
  have he4 : (((List.finRange 7).erase (4 : Fin 7)).map (M.d 4)) = [M.d 0 4, M.d 1 4, M.d 2 4, M.d 3 4, M.d 4 5, M.d 4 6] := by
    norm_num [List.finRange,List.ofFn_succ,hcanon40, hcanon41, hcanon42, hcanon43]
  rw [he4] at hp4
  have hperm4 := hp4.trans ((((((((((List.Perm.swap (M.d 4 5) (M.d 3 4) [M.d 4 6]).cons (M.d 2 4)).cons (M.d 1 4)).cons (M.d 0 4)).trans (((List.Perm.swap (M.d 4 5) (M.d 2 4) [M.d 3 4, M.d 4 6]).cons (M.d 1 4)).cons (M.d 0 4))).trans ((List.Perm.swap (M.d 4 5) (M.d 1 4) [M.d 2 4, M.d 3 4, M.d 4 6]).cons (M.d 0 4))).trans (((((List.Perm.swap (M.d 4 6) (M.d 3 4) []).cons (M.d 2 4)).cons (M.d 1 4)).cons (M.d 4 5)).cons (M.d 0 4))).trans ((((List.Perm.swap (M.d 4 6) (M.d 2 4) [M.d 3 4]).cons (M.d 1 4)).cons (M.d 4 5)).cons (M.d 0 4))).trans (((List.Perm.swap (M.d 4 6) (M.d 1 4) [M.d 2 4, M.d 3 4]).cons (M.d 4 5)).cons (M.d 0 4))))
  have hrow4 : M.rowxs 4 = [M.d 0 4, M.d 4 5, M.d 4 6, M.d 1 4, M.d 2 4, M.d 3 4] := hperm4.eq_of_pairwise' (M.row_sorted 4) hsort4
  have hsort5 : ([M.d 0 5, M.d 4 5, M.d 2 5, M.d 1 5, M.d 3 5, M.d 5 6] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp5 := M.row_perm 5
  have hcanon50 : M.d 5 0 = M.d 0 5 := M.symm 5 0 (by decide)
  have hcanon51 : M.d 5 1 = M.d 1 5 := M.symm 5 1 (by decide)
  have hcanon52 : M.d 5 2 = M.d 2 5 := M.symm 5 2 (by decide)
  have hcanon53 : M.d 5 3 = M.d 3 5 := M.symm 5 3 (by decide)
  have hcanon54 : M.d 5 4 = M.d 4 5 := M.symm 5 4 (by decide)
  have he5 : (((List.finRange 7).erase (5 : Fin 7)).map (M.d 5)) = [M.d 0 5, M.d 1 5, M.d 2 5, M.d 3 5, M.d 4 5, M.d 5 6] := by
    norm_num [List.finRange,List.ofFn_succ,hcanon50, hcanon51, hcanon52, hcanon53, hcanon54]
  rw [he5] at hp5
  have hperm5 := hp5.trans ((((((((List.Perm.swap (M.d 4 5) (M.d 3 5) [M.d 5 6]).cons (M.d 2 5)).cons (M.d 1 5)).cons (M.d 0 5)).trans (((List.Perm.swap (M.d 4 5) (M.d 2 5) [M.d 3 5, M.d 5 6]).cons (M.d 1 5)).cons (M.d 0 5))).trans ((List.Perm.swap (M.d 4 5) (M.d 1 5) [M.d 2 5, M.d 3 5, M.d 5 6]).cons (M.d 0 5))).trans (((List.Perm.swap (M.d 2 5) (M.d 1 5) [M.d 3 5, M.d 5 6]).cons (M.d 4 5)).cons (M.d 0 5))))
  have hrow5 : M.rowxs 5 = [M.d 0 5, M.d 4 5, M.d 2 5, M.d 1 5, M.d 3 5, M.d 5 6] := hperm5.eq_of_pairwise' (M.row_sorted 5) hsort5
  have hsort6 : ([M.d 0 6, M.d 4 6, M.d 1 6, M.d 2 6, M.d 3 6, M.d 5 6] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp6 := M.row_perm 6
  have hcanon60 : M.d 6 0 = M.d 0 6 := M.symm 6 0 (by decide)
  have hcanon61 : M.d 6 1 = M.d 1 6 := M.symm 6 1 (by decide)
  have hcanon62 : M.d 6 2 = M.d 2 6 := M.symm 6 2 (by decide)
  have hcanon63 : M.d 6 3 = M.d 3 6 := M.symm 6 3 (by decide)
  have hcanon64 : M.d 6 4 = M.d 4 6 := M.symm 6 4 (by decide)
  have hcanon65 : M.d 6 5 = M.d 5 6 := M.symm 6 5 (by decide)
  have he6 : (((List.finRange 7).erase (6 : Fin 7)).map (M.d 6)) = [M.d 0 6, M.d 1 6, M.d 2 6, M.d 3 6, M.d 4 6, M.d 5 6] := by
    norm_num [List.finRange,List.ofFn_succ,hcanon60, hcanon61, hcanon62, hcanon63, hcanon64, hcanon65]
  rw [he6] at hp6
  have hperm6 := hp6.trans (((((((List.Perm.swap (M.d 4 6) (M.d 3 6) [M.d 5 6]).cons (M.d 2 6)).cons (M.d 1 6)).cons (M.d 0 6)).trans (((List.Perm.swap (M.d 4 6) (M.d 2 6) [M.d 3 6, M.d 5 6]).cons (M.d 1 6)).cons (M.d 0 6))).trans ((List.Perm.swap (M.d 4 6) (M.d 1 6) [M.d 2 6, M.d 3 6, M.d 5 6]).cons (M.d 0 6))))
  have hrow6 : M.rowxs 6 = [M.d 0 6, M.d 4 6, M.d 1 6, M.d 2 6, M.d 3 6, M.d 5 6] := hperm6.eq_of_pairwise' (M.row_sorted 6) hsort6
  have htail43 : (M.d 1 4 - M.d 4 6) < 2 := n4_tail_gaps_lt_two M 4 hdef4 _ (by
    simp [modelGaps,hrow4,linearGaps])
  have htail24 : (M.d 2 6 - M.d 1 2) < 2 := n4_tail_gaps_lt_two M 2 hdef2 _ (by
    simp [modelGaps,hrow2,linearGaps])
  have htail55 : (M.d 5 6 - M.d 3 5) < 2 := n4_tail_gaps_lt_two M 5 hdef5 _ (by
    simp [modelGaps,hrow5,linearGaps])
  have hg62 : (M.d 1 6 - M.d 4 6) < 2 := by linarith only [htail43,htr146c]
  have hg63 : (M.d 2 6 - M.d 1 6) < 2 := by linarith only [htail24,htr126b]
  have hg65 : (M.d 5 6 - M.d 3 6) < 2 := by linarith only [htail55,htr356b]
  have hg64 : (M.d 3 6 - M.d 2 6) < 2 := by
    linarith only [htr346c,hc34b,hc45a,htr245b,htr125a,htr126a,hdelta1]
  have hg66 : (M.theta 6 + (4 + M.delta) - M.d 5 6) < 2 := by
    linarith only [ht6b,ht0a,hc01a,htr013a,htr135a,htr356a,hdelta1]
  have hpair : (M.d 0 6 - M.theta 6) + (M.d 4 6 - M.d 0 6) < 3 := by
    linarith only [htr234c,hc34b,ht45,ht56,htr146a,htr124c,hdelta1]
  have hn60 : 0 ≤ (M.d 0 6 - M.theta 6) := model_gaps_nonneg M 6 _ (by simp [modelGaps,hrow6,linearGaps])
  have hn61 : 0 ≤ (M.d 4 6 - M.d 0 6) := model_gaps_nonneg M 6 _ (by simp [modelGaps,hrow6,linearGaps])
  have hn62 : 0 ≤ (M.d 1 6 - M.d 4 6) := model_gaps_nonneg M 6 _ (by simp [modelGaps,hrow6,linearGaps])
  have hz62 : ⌊(M.d 1 6 - M.d 4 6)⌋₊ - 1 = 0 := by
    have hq : ⌊(M.d 1 6 - M.d 4 6)⌋₊ < 2 := (Nat.floor_lt hn62).mpr (by norm_num; exact hg62)
    omega
  have hn63 : 0 ≤ (M.d 2 6 - M.d 1 6) := model_gaps_nonneg M 6 _ (by simp [modelGaps,hrow6,linearGaps])
  have hz63 : ⌊(M.d 2 6 - M.d 1 6)⌋₊ - 1 = 0 := by
    have hq : ⌊(M.d 2 6 - M.d 1 6)⌋₊ < 2 := (Nat.floor_lt hn63).mpr (by norm_num; exact hg63)
    omega
  have hn64 : 0 ≤ (M.d 3 6 - M.d 2 6) := model_gaps_nonneg M 6 _ (by simp [modelGaps,hrow6,linearGaps])
  have hz64 : ⌊(M.d 3 6 - M.d 2 6)⌋₊ - 1 = 0 := by
    have hq : ⌊(M.d 3 6 - M.d 2 6)⌋₊ < 2 := (Nat.floor_lt hn64).mpr (by norm_num; exact hg64)
    omega
  have hn65 : 0 ≤ (M.d 5 6 - M.d 3 6) := model_gaps_nonneg M 6 _ (by simp [modelGaps,hrow6,linearGaps])
  have hz65 : ⌊(M.d 5 6 - M.d 3 6)⌋₊ - 1 = 0 := by
    have hq : ⌊(M.d 5 6 - M.d 3 6)⌋₊ < 2 := (Nat.floor_lt hn65).mpr (by norm_num; exact hg65)
    omega
  have hn66 : 0 ≤ (M.theta 6 + (4 + M.delta) - M.d 5 6) := model_gaps_nonneg M 6 _ (by simp [modelGaps,hrow6,linearGaps])
  have hz66 : ⌊(M.theta 6 + (4 + M.delta) - M.d 5 6)⌋₊ - 1 = 0 := by
    have hq : ⌊(M.theta 6 + (4 + M.delta) - M.d 5 6)⌋₊ < 2 := (Nat.floor_lt hn66).mpr (by norm_num; exact hg66)
    omega
  have hf0 := Nat.floor_le hn60
  have hf1 := Nat.floor_le hn61
  have hqR : ((⌊(M.d 0 6 - M.theta 6)⌋₊ + ⌊(M.d 4 6 - M.d 0 6)⌋₊ : ℕ) : ℝ) < 3 := by
    simp only [Nat.cast_add]
    linarith only [hf0,hf1,hpair]
  have hqN : ⌊(M.d 0 6 - M.theta 6)⌋₊ + ⌊(M.d 4 6 - M.d 0 6)⌋₊ < 3 := by exact_mod_cast hqR
  have hs := n4_low_score M 6 hdef6
  simp only [modelGaps,hrow6,linearGaps,score,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.cast_ofNat] at hs
  omega

#print axioms fixed_word_low6_probe
end Jsp404.N4R2CriticalKernel
