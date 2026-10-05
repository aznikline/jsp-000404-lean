import Jsp000404.SixExactFloorKernelPrimitives

/-! Representative exact-score certificate. A fixed orientation is an explicit
hypothesis only for this probe; public wrappers must split every triangle arm. -/
namespace Jsp404.SixExactFloorKernel

set_option maxHeartbeats 16000000 in
theorem n5_between_mask223 (M : SixModelCompression.ModelSix 5)
    (hhigh : (1/2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    (htri012 : M.d 1 2+1 ≤ M.d 0 1 ∧ M.d 1 2 < M.d 0 2 ∧ M.d 0 2 < M.d 0 1)
    (htri013 : M.d 1 3+1 ≤ M.d 0 1 ∧ M.d 1 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 1)
    (htri014 : M.d 1 4+1 ≤ M.d 0 1 ∧ M.d 1 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 1)
    (htri023 : M.d 2 3+1 ≤ M.d 0 2 ∧ M.d 2 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 2)
    (htri024 : M.d 2 4+1 ≤ M.d 0 2 ∧ M.d 2 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 2)
    (htri034 : M.d 0 3+1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (htri123 : M.d 2 3+1 ≤ M.d 1 2 ∧ M.d 2 3 < M.d 1 3 ∧ M.d 1 3 < M.d 1 2)
    (htri124 : M.d 2 4+1 ≤ M.d 1 2 ∧ M.d 2 4 < M.d 1 4 ∧ M.d 1 4 < M.d 1 2)
    (htri134 : M.d 1 3+1 ≤ M.d 3 4 ∧ M.d 1 3 < M.d 1 4 ∧ M.d 1 4 < M.d 3 4)
    (htri234 : M.d 2 3+1 ≤ M.d 3 4 ∧ M.d 2 3 < M.d 2 4 ∧ M.d 2 4 < M.d 3 4)
    : False := by
  have hdelta0 := hhigh
  have hdelta1 := M.hdelta.2
  obtain ⟨ht0a, ht0b⟩ := M.theta_bounds 0
  have ht01 := M.htheta (show (0 : Fin 5) < 1 from by decide)
  obtain ⟨ht1a, ht1b⟩ := M.theta_bounds 1
  have ht12 := M.htheta (show (1 : Fin 5) < 2 from by decide)
  obtain ⟨ht2a, ht2b⟩ := M.theta_bounds 2
  have ht23 := M.htheta (show (2 : Fin 5) < 3 from by decide)
  obtain ⟨ht3a, ht3b⟩ := M.theta_bounds 3
  have ht34 := M.htheta (show (3 : Fin 5) < 4 from by decide)
  obtain ⟨ht4a, ht4b⟩ := M.theta_bounds 4
  obtain ⟨hc01a, hc01b⟩ := M.corridor 0 1 (by decide)
  norm_num at hc01b
  obtain ⟨hc02a, hc02b⟩ := M.corridor 0 2 (by decide)
  norm_num at hc02b
  obtain ⟨hc03a, hc03b⟩ := M.corridor 0 3 (by decide)
  norm_num at hc03b
  obtain ⟨hc04a, hc04b⟩ := M.corridor 0 4 (by decide)
  norm_num at hc04b
  obtain ⟨hc12a, hc12b⟩ := M.corridor 1 2 (by decide)
  norm_num at hc12b
  obtain ⟨hc13a, hc13b⟩ := M.corridor 1 3 (by decide)
  norm_num at hc13b
  obtain ⟨hc14a, hc14b⟩ := M.corridor 1 4 (by decide)
  norm_num at hc14b
  obtain ⟨hc23a, hc23b⟩ := M.corridor 2 3 (by decide)
  norm_num at hc23b
  obtain ⟨hc24a, hc24b⟩ := M.corridor 2 4 (by decide)
  norm_num at hc24b
  obtain ⟨hc34a, hc34b⟩ := M.corridor 3 4 (by decide)
  norm_num at hc34b
  obtain ⟨htr012a, htr012b, htr012c⟩ := htri012
  obtain ⟨htr013a, htr013b, htr013c⟩ := htri013
  obtain ⟨htr014a, htr014b, htr014c⟩ := htri014
  obtain ⟨htr023a, htr023b, htr023c⟩ := htri023
  obtain ⟨htr024a, htr024b, htr024c⟩ := htri024
  obtain ⟨htr034a, htr034b, htr034c⟩ := htri034
  obtain ⟨htr123a, htr123b, htr123c⟩ := htri123
  obtain ⟨htr124a, htr124b, htr124c⟩ := htri124
  obtain ⟨htr134a, htr134b, htr134c⟩ := htri134
  obtain ⟨htr234a, htr234b, htr234c⟩ := htri234
  have hsort0 : ([M.d 0 3, M.d 0 4, M.d 0 2, M.d 0 1] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp0 := M.row_perm 0
  have he0 : (((List.finRange 5).erase (0 : Fin 5)).map (M.d 0)) = [M.d 0 1, M.d 0 2, M.d 0 3, M.d 0 4] := by
    norm_num [List.finRange, List.ofFn_succ]
  rw [he0] at hp0
  have hperm0 := hp0.trans (((((((List.Perm.swap (M.d 0 3) (M.d 0 2) [M.d 0 4]).cons (M.d 0 1)).trans (List.Perm.swap (M.d 0 3) (M.d 0 1) [M.d 0 2, M.d 0 4])).trans (((List.Perm.swap (M.d 0 4) (M.d 0 2) []).cons (M.d 0 1)).cons (M.d 0 3))).trans ((List.Perm.swap (M.d 0 4) (M.d 0 1) [M.d 0 2]).cons (M.d 0 3))).trans (((List.Perm.swap (M.d 0 2) (M.d 0 1) []).cons (M.d 0 4)).cons (M.d 0 3))))
  have hrow0 : M.rowxs 0 = [M.d 0 3, M.d 0 4, M.d 0 2, M.d 0 1] := hperm0.eq_of_pairwise' (M.row_sorted 0) hsort0
  have hrow_nonneg0 := SmallScoreGapBounds.model_gaps_nonneg M 0
  simp only [SmallScoreGapBounds.modelGaps, hrow0, StrongGapBudget.linearGaps] at hrow_nonneg0
  norm_num only [Nat.cast_ofNat] at hrow_nonneg0
  let s00 : ℕ := ⌊(M.d 0 3 - M.theta 0)⌋₊ - 1
  have hnonneg00 : 0 ≤ (M.d 0 3 - M.theta 0) := hrow_nonneg0 (M.d 0 3 - M.theta 0) (by simp)
  have hscore00a : (0 : ℝ) ≤ s00 := Nat.cast_nonneg s00
  have hbridge00 := score_gap_dichotomy (M.d 0 3 - M.theta 0) hnonneg00
  change (s00 = 0 ∧ (M.d 0 3 - M.theta 0) < 2) ∨ (1 ≤ s00 ∧ (s00 : ℝ)+1 ≤ (M.d 0 3 - M.theta 0) ∧ (M.d 0 3 - M.theta 0) < (s00 : ℝ)+2) at hbridge00
  let s01 : ℕ := ⌊(M.d 0 4 - M.d 0 3)⌋₊ - 1
  have hnonneg01 : 0 ≤ (M.d 0 4 - M.d 0 3) := hrow_nonneg0 (M.d 0 4 - M.d 0 3) (by simp)
  have hscore01a : (0 : ℝ) ≤ s01 := Nat.cast_nonneg s01
  have hbridge01 := score_gap_dichotomy (M.d 0 4 - M.d 0 3) hnonneg01
  change (s01 = 0 ∧ (M.d 0 4 - M.d 0 3) < 2) ∨ (1 ≤ s01 ∧ (s01 : ℝ)+1 ≤ (M.d 0 4 - M.d 0 3) ∧ (M.d 0 4 - M.d 0 3) < (s01 : ℝ)+2) at hbridge01
  let s02 : ℕ := ⌊(M.d 0 2 - M.d 0 4)⌋₊ - 1
  have hnonneg02 : 0 ≤ (M.d 0 2 - M.d 0 4) := hrow_nonneg0 (M.d 0 2 - M.d 0 4) (by simp)
  have hscore02a : (0 : ℝ) ≤ s02 := Nat.cast_nonneg s02
  have hbridge02 := score_gap_dichotomy (M.d 0 2 - M.d 0 4) hnonneg02
  change (s02 = 0 ∧ (M.d 0 2 - M.d 0 4) < 2) ∨ (1 ≤ s02 ∧ (s02 : ℝ)+1 ≤ (M.d 0 2 - M.d 0 4) ∧ (M.d 0 2 - M.d 0 4) < (s02 : ℝ)+2) at hbridge02
  let s03 : ℕ := ⌊(M.d 0 1 - M.d 0 2)⌋₊ - 1
  have hnonneg03 : 0 ≤ (M.d 0 1 - M.d 0 2) := hrow_nonneg0 (M.d 0 1 - M.d 0 2) (by simp)
  have hscore03a : (0 : ℝ) ≤ s03 := Nat.cast_nonneg s03
  have hbridge03 := score_gap_dichotomy (M.d 0 1 - M.d 0 2) hnonneg03
  change (s03 = 0 ∧ (M.d 0 1 - M.d 0 2) < 2) ∨ (1 ≤ s03 ∧ (s03 : ℝ)+1 ≤ (M.d 0 1 - M.d 0 2) ∧ (M.d 0 1 - M.d 0 2) < (s03 : ℝ)+2) at hbridge03
  let s04 : ℕ := ⌊(M.theta 0 + (5 + M.delta) - M.d 0 1)⌋₊ - 1
  have hnonneg04 : 0 ≤ (M.theta 0 + (5 + M.delta) - M.d 0 1) := hrow_nonneg0 (M.theta 0 + (5 + M.delta) - M.d 0 1) (by simp)
  have hscore04a : (0 : ℝ) ≤ s04 := Nat.cast_nonneg s04
  have hbridge04 := score_gap_dichotomy (M.theta 0 + (5 + M.delta) - M.d 0 1) hnonneg04
  change (s04 = 0 ∧ (M.theta 0 + (5 + M.delta) - M.d 0 1) < 2) ∨ (1 ≤ s04 ∧ (s04 : ℝ)+1 ≤ (M.theta 0 + (5 + M.delta) - M.d 0 1) ∧ (M.theta 0 + (5 + M.delta) - M.d 0 1) < (s04 : ℝ)+2) at hbridge04
  have hsum_nat0 : s00 + (s01 + (s02 + (s03 + (s04)))) = 3 := by
    have h := SmallScoreGapBounds.model_score M 0 2 hdef0
    simp only [SmallScoreGapBounds.modelGaps, hrow0, StrongGapBudget.linearGaps, StrongGapBudget.score, List.map_cons, List.sum_cons, List.sum_nil] at h
    change (s00 + (s01 + (s02 + (s03 + (s04 + 0))))) + 2 = 5 at h
    omega
  have hsum0 : (s00 : ℝ) + ((s01 : ℝ) + ((s02 : ℝ) + ((s03 : ℝ) + ((s04 : ℝ))))) = 3 := by
    have h : s00 + (s01 + (s02 + (s03 + (s04)))) = 3 := hsum_nat0
    exact_mod_cast h
  have hscore00b : (s00 : ℝ) ≤ 3 := by
    have h : s00 ≤ 3 := by omega
    exact_mod_cast h
  have hscore01b : (s01 : ℝ) ≤ 3 := by
    have h : s01 ≤ 3 := by omega
    exact_mod_cast h
  have hscore02b : (s02 : ℝ) ≤ 3 := by
    have h : s02 ≤ 3 := by omega
    exact_mod_cast h
  have hscore03b : (s03 : ℝ) ≤ 3 := by
    have h : s03 ≤ 3 := by omega
    exact_mod_cast h
  have hscore04b : (s04 : ℝ) ≤ 3 := by
    have h : s04 ≤ 3 := by omega
    exact_mod_cast h
  have hsort1 : ([M.d 1 3, M.d 1 4, M.d 1 2, M.d 0 1] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp1 := M.row_perm 1
  have hcanon10 : M.d 1 0 = M.d 0 1 := M.symm 1 0 (by decide)
  have he1 : (((List.finRange 5).erase (1 : Fin 5)).map (M.d 1)) = [M.d 0 1, M.d 1 2, M.d 1 3, M.d 1 4] := by
    norm_num [List.finRange, List.ofFn_succ, hcanon10]
  rw [he1] at hp1
  have hperm1 := hp1.trans (((((((List.Perm.swap (M.d 1 3) (M.d 1 2) [M.d 1 4]).cons (M.d 0 1)).trans (List.Perm.swap (M.d 1 3) (M.d 0 1) [M.d 1 2, M.d 1 4])).trans (((List.Perm.swap (M.d 1 4) (M.d 1 2) []).cons (M.d 0 1)).cons (M.d 1 3))).trans ((List.Perm.swap (M.d 1 4) (M.d 0 1) [M.d 1 2]).cons (M.d 1 3))).trans (((List.Perm.swap (M.d 1 2) (M.d 0 1) []).cons (M.d 1 4)).cons (M.d 1 3))))
  have hrow1 : M.rowxs 1 = [M.d 1 3, M.d 1 4, M.d 1 2, M.d 0 1] := hperm1.eq_of_pairwise' (M.row_sorted 1) hsort1
  have hrow_nonneg1 := SmallScoreGapBounds.model_gaps_nonneg M 1
  simp only [SmallScoreGapBounds.modelGaps, hrow1, StrongGapBudget.linearGaps] at hrow_nonneg1
  norm_num only [Nat.cast_ofNat] at hrow_nonneg1
  let s10 : ℕ := ⌊(M.d 1 3 - M.theta 1)⌋₊ - 1
  have hnonneg10 : 0 ≤ (M.d 1 3 - M.theta 1) := hrow_nonneg1 (M.d 1 3 - M.theta 1) (by simp)
  have hscore10a : (0 : ℝ) ≤ s10 := Nat.cast_nonneg s10
  have hbridge10 := score_gap_dichotomy (M.d 1 3 - M.theta 1) hnonneg10
  change (s10 = 0 ∧ (M.d 1 3 - M.theta 1) < 2) ∨ (1 ≤ s10 ∧ (s10 : ℝ)+1 ≤ (M.d 1 3 - M.theta 1) ∧ (M.d 1 3 - M.theta 1) < (s10 : ℝ)+2) at hbridge10
  let s11 : ℕ := ⌊(M.d 1 4 - M.d 1 3)⌋₊ - 1
  have hnonneg11 : 0 ≤ (M.d 1 4 - M.d 1 3) := hrow_nonneg1 (M.d 1 4 - M.d 1 3) (by simp)
  have hscore11a : (0 : ℝ) ≤ s11 := Nat.cast_nonneg s11
  have hbridge11 := score_gap_dichotomy (M.d 1 4 - M.d 1 3) hnonneg11
  change (s11 = 0 ∧ (M.d 1 4 - M.d 1 3) < 2) ∨ (1 ≤ s11 ∧ (s11 : ℝ)+1 ≤ (M.d 1 4 - M.d 1 3) ∧ (M.d 1 4 - M.d 1 3) < (s11 : ℝ)+2) at hbridge11
  let s12 : ℕ := ⌊(M.d 1 2 - M.d 1 4)⌋₊ - 1
  have hnonneg12 : 0 ≤ (M.d 1 2 - M.d 1 4) := hrow_nonneg1 (M.d 1 2 - M.d 1 4) (by simp)
  have hscore12a : (0 : ℝ) ≤ s12 := Nat.cast_nonneg s12
  have hbridge12 := score_gap_dichotomy (M.d 1 2 - M.d 1 4) hnonneg12
  change (s12 = 0 ∧ (M.d 1 2 - M.d 1 4) < 2) ∨ (1 ≤ s12 ∧ (s12 : ℝ)+1 ≤ (M.d 1 2 - M.d 1 4) ∧ (M.d 1 2 - M.d 1 4) < (s12 : ℝ)+2) at hbridge12
  let s13 : ℕ := ⌊(M.d 0 1 - M.d 1 2)⌋₊ - 1
  have hnonneg13 : 0 ≤ (M.d 0 1 - M.d 1 2) := hrow_nonneg1 (M.d 0 1 - M.d 1 2) (by simp)
  have hscore13a : (0 : ℝ) ≤ s13 := Nat.cast_nonneg s13
  have hbridge13 := score_gap_dichotomy (M.d 0 1 - M.d 1 2) hnonneg13
  change (s13 = 0 ∧ (M.d 0 1 - M.d 1 2) < 2) ∨ (1 ≤ s13 ∧ (s13 : ℝ)+1 ≤ (M.d 0 1 - M.d 1 2) ∧ (M.d 0 1 - M.d 1 2) < (s13 : ℝ)+2) at hbridge13
  let s14 : ℕ := ⌊(M.theta 1 + (5 + M.delta) - M.d 0 1)⌋₊ - 1
  have hnonneg14 : 0 ≤ (M.theta 1 + (5 + M.delta) - M.d 0 1) := hrow_nonneg1 (M.theta 1 + (5 + M.delta) - M.d 0 1) (by simp)
  have hscore14a : (0 : ℝ) ≤ s14 := Nat.cast_nonneg s14
  have hbridge14 := score_gap_dichotomy (M.theta 1 + (5 + M.delta) - M.d 0 1) hnonneg14
  change (s14 = 0 ∧ (M.theta 1 + (5 + M.delta) - M.d 0 1) < 2) ∨ (1 ≤ s14 ∧ (s14 : ℝ)+1 ≤ (M.theta 1 + (5 + M.delta) - M.d 0 1) ∧ (M.theta 1 + (5 + M.delta) - M.d 0 1) < (s14 : ℝ)+2) at hbridge14
  have hsum_nat1 : s10 + (s11 + (s12 + (s13 + (s14)))) = 2 := by
    have h := SmallScoreGapBounds.model_score M 1 3 hdef1
    simp only [SmallScoreGapBounds.modelGaps, hrow1, StrongGapBudget.linearGaps, StrongGapBudget.score, List.map_cons, List.sum_cons, List.sum_nil] at h
    change (s10 + (s11 + (s12 + (s13 + (s14 + 0))))) + 3 = 5 at h
    omega
  have hsum1 : (s10 : ℝ) + ((s11 : ℝ) + ((s12 : ℝ) + ((s13 : ℝ) + ((s14 : ℝ))))) = 2 := by
    have h : s10 + (s11 + (s12 + (s13 + (s14)))) = 2 := hsum_nat1
    exact_mod_cast h
  have hscore10b : (s10 : ℝ) ≤ 2 := by
    have h : s10 ≤ 2 := by omega
    exact_mod_cast h
  have hscore11b : (s11 : ℝ) ≤ 2 := by
    have h : s11 ≤ 2 := by omega
    exact_mod_cast h
  have hscore12b : (s12 : ℝ) ≤ 2 := by
    have h : s12 ≤ 2 := by omega
    exact_mod_cast h
  have hscore13b : (s13 : ℝ) ≤ 2 := by
    have h : s13 ≤ 2 := by omega
    exact_mod_cast h
  have hscore14b : (s14 : ℝ) ≤ 2 := by
    have h : s14 ≤ 2 := by omega
    exact_mod_cast h
  have hsort3 : ([M.d 2 3, M.d 1 3, M.d 0 3, M.d 3 4] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp3 := M.row_perm 3
  have hcanon30 : M.d 3 0 = M.d 0 3 := M.symm 3 0 (by decide)
  have hcanon31 : M.d 3 1 = M.d 1 3 := M.symm 3 1 (by decide)
  have hcanon32 : M.d 3 2 = M.d 2 3 := M.symm 3 2 (by decide)
  have he3 : (((List.finRange 5).erase (3 : Fin 5)).map (M.d 3)) = [M.d 0 3, M.d 1 3, M.d 2 3, M.d 3 4] := by
    norm_num [List.finRange, List.ofFn_succ, hcanon30, hcanon31, hcanon32]
  rw [he3] at hp3
  have hperm3 := hp3.trans (((((List.Perm.swap (M.d 2 3) (M.d 1 3) [M.d 3 4]).cons (M.d 0 3)).trans (List.Perm.swap (M.d 2 3) (M.d 0 3) [M.d 1 3, M.d 3 4])).trans ((List.Perm.swap (M.d 1 3) (M.d 0 3) [M.d 3 4]).cons (M.d 2 3))))
  have hrow3 : M.rowxs 3 = [M.d 2 3, M.d 1 3, M.d 0 3, M.d 3 4] := hperm3.eq_of_pairwise' (M.row_sorted 3) hsort3
  have hrow_nonneg3 := SmallScoreGapBounds.model_gaps_nonneg M 3
  simp only [SmallScoreGapBounds.modelGaps, hrow3, StrongGapBudget.linearGaps] at hrow_nonneg3
  norm_num only [Nat.cast_ofNat] at hrow_nonneg3
  let s30 : ℕ := ⌊(M.d 2 3 - M.theta 3)⌋₊ - 1
  have hnonneg30 : 0 ≤ (M.d 2 3 - M.theta 3) := hrow_nonneg3 (M.d 2 3 - M.theta 3) (by simp)
  have hscore30a : (0 : ℝ) ≤ s30 := Nat.cast_nonneg s30
  have hbridge30 := score_gap_dichotomy (M.d 2 3 - M.theta 3) hnonneg30
  change (s30 = 0 ∧ (M.d 2 3 - M.theta 3) < 2) ∨ (1 ≤ s30 ∧ (s30 : ℝ)+1 ≤ (M.d 2 3 - M.theta 3) ∧ (M.d 2 3 - M.theta 3) < (s30 : ℝ)+2) at hbridge30
  let s31 : ℕ := ⌊(M.d 1 3 - M.d 2 3)⌋₊ - 1
  have hnonneg31 : 0 ≤ (M.d 1 3 - M.d 2 3) := hrow_nonneg3 (M.d 1 3 - M.d 2 3) (by simp)
  have hscore31a : (0 : ℝ) ≤ s31 := Nat.cast_nonneg s31
  have hbridge31 := score_gap_dichotomy (M.d 1 3 - M.d 2 3) hnonneg31
  change (s31 = 0 ∧ (M.d 1 3 - M.d 2 3) < 2) ∨ (1 ≤ s31 ∧ (s31 : ℝ)+1 ≤ (M.d 1 3 - M.d 2 3) ∧ (M.d 1 3 - M.d 2 3) < (s31 : ℝ)+2) at hbridge31
  let s32 : ℕ := ⌊(M.d 0 3 - M.d 1 3)⌋₊ - 1
  have hnonneg32 : 0 ≤ (M.d 0 3 - M.d 1 3) := hrow_nonneg3 (M.d 0 3 - M.d 1 3) (by simp)
  have hscore32a : (0 : ℝ) ≤ s32 := Nat.cast_nonneg s32
  have hbridge32 := score_gap_dichotomy (M.d 0 3 - M.d 1 3) hnonneg32
  change (s32 = 0 ∧ (M.d 0 3 - M.d 1 3) < 2) ∨ (1 ≤ s32 ∧ (s32 : ℝ)+1 ≤ (M.d 0 3 - M.d 1 3) ∧ (M.d 0 3 - M.d 1 3) < (s32 : ℝ)+2) at hbridge32
  let s33 : ℕ := ⌊(M.d 3 4 - M.d 0 3)⌋₊ - 1
  have hnonneg33 : 0 ≤ (M.d 3 4 - M.d 0 3) := hrow_nonneg3 (M.d 3 4 - M.d 0 3) (by simp)
  have hscore33a : (0 : ℝ) ≤ s33 := Nat.cast_nonneg s33
  have hbridge33 := score_gap_dichotomy (M.d 3 4 - M.d 0 3) hnonneg33
  change (s33 = 0 ∧ (M.d 3 4 - M.d 0 3) < 2) ∨ (1 ≤ s33 ∧ (s33 : ℝ)+1 ≤ (M.d 3 4 - M.d 0 3) ∧ (M.d 3 4 - M.d 0 3) < (s33 : ℝ)+2) at hbridge33
  let s34 : ℕ := ⌊(M.theta 3 + (5 + M.delta) - M.d 3 4)⌋₊ - 1
  have hnonneg34 : 0 ≤ (M.theta 3 + (5 + M.delta) - M.d 3 4) := hrow_nonneg3 (M.theta 3 + (5 + M.delta) - M.d 3 4) (by simp)
  have hscore34a : (0 : ℝ) ≤ s34 := Nat.cast_nonneg s34
  have hbridge34 := score_gap_dichotomy (M.theta 3 + (5 + M.delta) - M.d 3 4) hnonneg34
  change (s34 = 0 ∧ (M.theta 3 + (5 + M.delta) - M.d 3 4) < 2) ∨ (1 ≤ s34 ∧ (s34 : ℝ)+1 ≤ (M.theta 3 + (5 + M.delta) - M.d 3 4) ∧ (M.theta 3 + (5 + M.delta) - M.d 3 4) < (s34 : ℝ)+2) at hbridge34
  have hsum_nat3 : s30 + (s31 + (s32 + (s33 + (s34)))) = 2 := by
    have h := SmallScoreGapBounds.model_score M 3 3 hdef3
    simp only [SmallScoreGapBounds.modelGaps, hrow3, StrongGapBudget.linearGaps, StrongGapBudget.score, List.map_cons, List.sum_cons, List.sum_nil] at h
    change (s30 + (s31 + (s32 + (s33 + (s34 + 0))))) + 3 = 5 at h
    omega
  have hsum3 : (s30 : ℝ) + ((s31 : ℝ) + ((s32 : ℝ) + ((s33 : ℝ) + ((s34 : ℝ))))) = 2 := by
    have h : s30 + (s31 + (s32 + (s33 + (s34)))) = 2 := hsum_nat3
    exact_mod_cast h
  have hscore30b : (s30 : ℝ) ≤ 2 := by
    have h : s30 ≤ 2 := by omega
    exact_mod_cast h
  have hscore31b : (s31 : ℝ) ≤ 2 := by
    have h : s31 ≤ 2 := by omega
    exact_mod_cast h
  have hscore32b : (s32 : ℝ) ≤ 2 := by
    have h : s32 ≤ 2 := by omega
    exact_mod_cast h
  have hscore33b : (s33 : ℝ) ≤ 2 := by
    have h : s33 ≤ 2 := by omega
    exact_mod_cast h
  have hscore34b : (s34 : ℝ) ≤ 2 := by
    have h : s34 ≤ 2 := by omega
    exact_mod_cast h
  have hsort4 : ([M.d 2 4, M.d 1 4, M.d 0 4, M.d 3 4] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp4 := M.row_perm 4
  have hcanon40 : M.d 4 0 = M.d 0 4 := M.symm 4 0 (by decide)
  have hcanon41 : M.d 4 1 = M.d 1 4 := M.symm 4 1 (by decide)
  have hcanon42 : M.d 4 2 = M.d 2 4 := M.symm 4 2 (by decide)
  have hcanon43 : M.d 4 3 = M.d 3 4 := M.symm 4 3 (by decide)
  have he4 : (((List.finRange 5).erase (4 : Fin 5)).map (M.d 4)) = [M.d 0 4, M.d 1 4, M.d 2 4, M.d 3 4] := by
    norm_num [List.finRange, List.ofFn_succ, hcanon40, hcanon41, hcanon42, hcanon43]
  rw [he4] at hp4
  have hperm4 := hp4.trans (((((List.Perm.swap (M.d 2 4) (M.d 1 4) [M.d 3 4]).cons (M.d 0 4)).trans (List.Perm.swap (M.d 2 4) (M.d 0 4) [M.d 1 4, M.d 3 4])).trans ((List.Perm.swap (M.d 1 4) (M.d 0 4) [M.d 3 4]).cons (M.d 2 4))))
  have hrow4 : M.rowxs 4 = [M.d 2 4, M.d 1 4, M.d 0 4, M.d 3 4] := hperm4.eq_of_pairwise' (M.row_sorted 4) hsort4
  have hrow_nonneg4 := SmallScoreGapBounds.model_gaps_nonneg M 4
  simp only [SmallScoreGapBounds.modelGaps, hrow4, StrongGapBudget.linearGaps] at hrow_nonneg4
  norm_num only [Nat.cast_ofNat] at hrow_nonneg4
  let s40 : ℕ := ⌊(M.d 2 4 - M.theta 4)⌋₊ - 1
  have hnonneg40 : 0 ≤ (M.d 2 4 - M.theta 4) := hrow_nonneg4 (M.d 2 4 - M.theta 4) (by simp)
  have hscore40a : (0 : ℝ) ≤ s40 := Nat.cast_nonneg s40
  have hbridge40 := score_gap_dichotomy (M.d 2 4 - M.theta 4) hnonneg40
  change (s40 = 0 ∧ (M.d 2 4 - M.theta 4) < 2) ∨ (1 ≤ s40 ∧ (s40 : ℝ)+1 ≤ (M.d 2 4 - M.theta 4) ∧ (M.d 2 4 - M.theta 4) < (s40 : ℝ)+2) at hbridge40
  let s41 : ℕ := ⌊(M.d 1 4 - M.d 2 4)⌋₊ - 1
  have hnonneg41 : 0 ≤ (M.d 1 4 - M.d 2 4) := hrow_nonneg4 (M.d 1 4 - M.d 2 4) (by simp)
  have hscore41a : (0 : ℝ) ≤ s41 := Nat.cast_nonneg s41
  have hbridge41 := score_gap_dichotomy (M.d 1 4 - M.d 2 4) hnonneg41
  change (s41 = 0 ∧ (M.d 1 4 - M.d 2 4) < 2) ∨ (1 ≤ s41 ∧ (s41 : ℝ)+1 ≤ (M.d 1 4 - M.d 2 4) ∧ (M.d 1 4 - M.d 2 4) < (s41 : ℝ)+2) at hbridge41
  let s42 : ℕ := ⌊(M.d 0 4 - M.d 1 4)⌋₊ - 1
  have hnonneg42 : 0 ≤ (M.d 0 4 - M.d 1 4) := hrow_nonneg4 (M.d 0 4 - M.d 1 4) (by simp)
  have hscore42a : (0 : ℝ) ≤ s42 := Nat.cast_nonneg s42
  have hbridge42 := score_gap_dichotomy (M.d 0 4 - M.d 1 4) hnonneg42
  change (s42 = 0 ∧ (M.d 0 4 - M.d 1 4) < 2) ∨ (1 ≤ s42 ∧ (s42 : ℝ)+1 ≤ (M.d 0 4 - M.d 1 4) ∧ (M.d 0 4 - M.d 1 4) < (s42 : ℝ)+2) at hbridge42
  let s43 : ℕ := ⌊(M.d 3 4 - M.d 0 4)⌋₊ - 1
  have hnonneg43 : 0 ≤ (M.d 3 4 - M.d 0 4) := hrow_nonneg4 (M.d 3 4 - M.d 0 4) (by simp)
  have hscore43a : (0 : ℝ) ≤ s43 := Nat.cast_nonneg s43
  have hbridge43 := score_gap_dichotomy (M.d 3 4 - M.d 0 4) hnonneg43
  change (s43 = 0 ∧ (M.d 3 4 - M.d 0 4) < 2) ∨ (1 ≤ s43 ∧ (s43 : ℝ)+1 ≤ (M.d 3 4 - M.d 0 4) ∧ (M.d 3 4 - M.d 0 4) < (s43 : ℝ)+2) at hbridge43
  let s44 : ℕ := ⌊(M.theta 4 + (5 + M.delta) - M.d 3 4)⌋₊ - 1
  have hnonneg44 : 0 ≤ (M.theta 4 + (5 + M.delta) - M.d 3 4) := hrow_nonneg4 (M.theta 4 + (5 + M.delta) - M.d 3 4) (by simp)
  have hscore44a : (0 : ℝ) ≤ s44 := Nat.cast_nonneg s44
  have hbridge44 := score_gap_dichotomy (M.theta 4 + (5 + M.delta) - M.d 3 4) hnonneg44
  change (s44 = 0 ∧ (M.theta 4 + (5 + M.delta) - M.d 3 4) < 2) ∨ (1 ≤ s44 ∧ (s44 : ℝ)+1 ≤ (M.theta 4 + (5 + M.delta) - M.d 3 4) ∧ (M.theta 4 + (5 + M.delta) - M.d 3 4) < (s44 : ℝ)+2) at hbridge44
  have hsum_nat4 : s40 + (s41 + (s42 + (s43 + (s44)))) = 3 := by
    have h := SmallScoreGapBounds.model_score M 4 2 hdef4
    simp only [SmallScoreGapBounds.modelGaps, hrow4, StrongGapBudget.linearGaps, StrongGapBudget.score, List.map_cons, List.sum_cons, List.sum_nil] at h
    change (s40 + (s41 + (s42 + (s43 + (s44 + 0))))) + 2 = 5 at h
    omega
  have hsum4 : (s40 : ℝ) + ((s41 : ℝ) + ((s42 : ℝ) + ((s43 : ℝ) + ((s44 : ℝ))))) = 3 := by
    have h : s40 + (s41 + (s42 + (s43 + (s44)))) = 3 := hsum_nat4
    exact_mod_cast h
  have hscore40b : (s40 : ℝ) ≤ 3 := by
    have h : s40 ≤ 3 := by omega
    exact_mod_cast h
  have hscore41b : (s41 : ℝ) ≤ 3 := by
    have h : s41 ≤ 3 := by omega
    exact_mod_cast h
  have hscore42b : (s42 : ℝ) ≤ 3 := by
    have h : s42 ≤ 3 := by omega
    exact_mod_cast h
  have hscore43b : (s43 : ℝ) ≤ 3 := by
    have h : s43 ≤ 3 := by omega
    exact_mod_cast h
  have hscore44b : (s44 : ℝ) ≤ 3 := by
    have h : s44 ≤ 3 := by omega
    exact_mod_cast h
  rcases hbridge00 with ⟨hzero00, hgap00b⟩ | ⟨hpositive00, hgap00b, hgap00c⟩
  ·
    have hgap00a : (s00 : ℝ) = 0 := by exact_mod_cast hzero00
    rcases hbridge10 with ⟨hzero10, hgap10b⟩ | ⟨hpositive10, hgap10b, hgap10c⟩
    ·
      have hgap10a : (s10 : ℝ) = 0 := by exact_mod_cast hzero10
      rcases hbridge11 with ⟨hzero11, hgap11b⟩ | ⟨hpositive11, hgap11b, hgap11c⟩
      ·
        have hgap11a : (s11 : ℝ) = 0 := by exact_mod_cast hzero11
        rcases hbridge12 with ⟨hzero12, hgap12b⟩ | ⟨hpositive12, hgap12b, hgap12c⟩
        ·
          have hgap12a : (s12 : ℝ) = 0 := by exact_mod_cast hzero12
          rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
          ·
            have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
            rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
            ·
              have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
              linarith only [hgap11a, hsum1, hgap10a, hgap14a, hgap12a, hgap13a]
            ·
              have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
              linarith only [hgap12a, hc23a, htr124a, hgap13a, hgap14b, hgap10a, hsum1, htr234b, ht12, htr012a, hdelta1, hgap11a]
          ·
            have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
            rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
            ·
              have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
              linarith only [hc23a, hgap11a, ht12, hc01b, htr124a, htr234b, hdelta1, hgap10a, hgap14a, hsum1, hgap13b, hgap12a]
            ·
              have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
              linarith only [hc23a, htr124a, hgap13b, htr234b, hgap14a, hgap14b, hgap13a, hdelta1, ht12]
        ·
          have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
          rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
          ·
            have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
            rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
            ·
              have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
              linarith only [hdelta1, hgap10a, hgap11a, hsum1, htr012a, hgap14a, ht12, hgap13a, htr134b, hgap12b, hc01b, hc23a, htr123b]
            ·
              have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
              linarith only [hgap12b, htr123b, ht12, hgap14b, htr012a, hdelta1, htr134b, hc23a, hgap12a, hgap14a]
          ·
            have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
            linarith only [htr134b, hc01b, hgap12b, hgap13b, htr123b, hgap13a, hdelta1, hc23a, hgap12a, ht12]
      ·
        have hgap11a : (1 : ℝ) ≤ s11 := by exact_mod_cast hpositive11
        rcases hbridge12 with ⟨hzero12, hgap12b⟩ | ⟨hpositive12, hgap12b, hgap12c⟩
        ·
          have hgap12a : (s12 : ℝ) = 0 := by exact_mod_cast hzero12
          rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
          ·
            have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
            rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
            ·
              have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
              linarith only [hgap14a, htr123b, htr014a, hgap11b, hc01b, hgap10a, hgap12a, hc23a, hdelta1, hsum1, ht12, hgap13a]
            ·
              have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
              linarith only [hgap14b, ht12, htr012a, hc23a, hgap11b, hgap11a, htr123b, htr124c, hdelta1, hgap14a]
          ·
            have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
            linarith only [hgap11b, htr124c, hc01b, hgap13a, ht12, hgap11a, htr123b, hgap13b, hdelta1, hc23a]
        ·
          have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
          linarith only [hc23a, htr123b, hc01b, hgap11a, htr012a, hgap11b, hdelta1, hgap12b, ht12, hgap12a]
    ·
      have hgap10a : (1 : ℝ) ≤ s10 := by exact_mod_cast hpositive10
      linarith only [ht01, htr013b, hgap10a, hgap00b, hgap10b]
  ·
    have hgap00a : (1 : ℝ) ≤ s00 := by exact_mod_cast hpositive00
    rcases hbridge01 with ⟨hzero01, hgap01b⟩ | ⟨hpositive01, hgap01b, hgap01c⟩
    ·
      have hgap01a : (s01 : ℝ) = 0 := by exact_mod_cast hzero01
      rcases hbridge02 with ⟨hzero02, hgap02b⟩ | ⟨hpositive02, hgap02b, hgap02c⟩
      ·
        have hgap02a : (s02 : ℝ) = 0 := by exact_mod_cast hzero02
        rcases hbridge03 with ⟨hzero03, hgap03b⟩ | ⟨hpositive03, hgap03b, hgap03c⟩
        ·
          have hgap03a : (s03 : ℝ) = 0 := by exact_mod_cast hzero03
          rcases hbridge04 with ⟨hzero04, hgap04b⟩ | ⟨hpositive04, hgap04b, hgap04c⟩
          ·
            have hgap04a : (s04 : ℝ) = 0 := by exact_mod_cast hzero04
            rcases hbridge40 with ⟨hzero40, hgap40b⟩ | ⟨hpositive40, hgap40b, hgap40c⟩
            ·
              have hgap40a : (s40 : ℝ) = 0 := by exact_mod_cast hzero40
              rcases hbridge10 with ⟨hzero10, hgap10b⟩ | ⟨hpositive10, hgap10b, hgap10c⟩
              ·
                have hgap10a : (s10 : ℝ) = 0 := by exact_mod_cast hzero10
                rcases hbridge41 with ⟨hzero41, hgap41b⟩ | ⟨hpositive41, hgap41b, hgap41c⟩
                ·
                  have hgap41a : (s41 : ℝ) = 0 := by exact_mod_cast hzero41
                  rcases hbridge42 with ⟨hzero42, hgap42b⟩ | ⟨hpositive42, hgap42b, hgap42c⟩
                  ·
                    have hgap42a : (s42 : ℝ) = 0 := by exact_mod_cast hzero42
                    rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                    ·
                      have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                      rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                      ·
                        have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                        linarith only [hgap40a, hsum4, hgap42a, hgap44a, hgap41a, hgap43a]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [hgap42a, ht0a, hdelta1, ht4b, hsum0, htr034a, hgap01a, hgap04a, hsum4, hgap43a, hgap03a, hgap41a, hgap02a, hgap44b, hgap00b, hgap40a]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [hsum0, ht0a, hgap01a, ht4b, htr034b, hgap43a, hgap00b, hgap43b, hgap04a, hdelta1, hgap02a, hc34b, hgap03a]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                    ·
                      have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                      rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                      ·
                        have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                        linarith only [hsum4, hdelta1, ht12, hgap43a, htr134b, htr123b, hgap44a, hgap40a, hc23a, htr024c, hc01b, hgap41a, hgap42b, htr012c]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [hgap00b, ht0a, hgap02a, hgap44b, hgap44a, hgap03a, htr034a, ht4b, hsum0, hgap04a, hgap01a, hdelta1]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [hgap43b, hgap01a, hgap03a, hsum0, hc34b, ht4b, hdelta1, hgap43a, hgap00b, ht0a, htr034b, hgap04a, hgap02a]
                ·
                  have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                  rcases hbridge42 with ⟨hzero42, hgap42b⟩ | ⟨hpositive42, hgap42b, hgap42c⟩
                  ·
                    have hgap42a : (s42 : ℝ) = 0 := by exact_mod_cast hzero42
                    rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                    ·
                      have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                      rcases hbridge11 with ⟨hzero11, hgap11b⟩ | ⟨hpositive11, hgap11b, hgap11c⟩
                      ·
                        have hgap11a : (s11 : ℝ) = 0 := by exact_mod_cast hzero11
                        rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                        ·
                          have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                          linarith only [hdelta1, hgap41b, hc23a, hgap44a, hgap42a, hc01b, htr234b, hgap43a, ht12, hsum4, htr014a, hgap40a]
                        ·
                          have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                          linarith only [hgap41b, hgap03a, hgap01a, hgap04a, htr034a, ht0a, hc01b, ht4b, ht12, hgap43a, hsum4, hgap00b, hgap02a, hgap40a, htr124c, htr012a, hc23a, hgap42a, hgap44b, hdelta1, hsum0, htr234b]
                      ·
                        have hgap11a : (1 : ℝ) ≤ s11 := by exact_mod_cast hpositive11
                        rcases hbridge12 with ⟨hzero12, hgap12b⟩ | ⟨hpositive12, hgap12b, hgap12c⟩
                        ·
                          have hgap12a : (s12 : ℝ) = 0 := by exact_mod_cast hzero12
                          rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                          ·
                            have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                            linarith only [hdelta1, hgap44a, hc01b, hgap40a, htr014a, hgap42a, hsum4, hgap41b, hgap43a, htr234b, hc23a, ht12]
                          ·
                            have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                            linarith only [htr234b, ht0a, hsum0, hgap01a, hgap41b, hgap02a, hdelta1, ht12, ht4b, htr034a, hgap42a, hc01b, hgap44b, hgap40a, hgap04a, hsum4, hgap03a, htr014a, hc23a, hgap00b, hgap43a]
                        ·
                          have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
                          linarith only [hdelta1, ht12, hc01b, htr234b, hgap41a, htr012a, hgap41b, hgap12b, hc23a, hgap12a]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [htr034b, hsum0, hgap04a, hgap02a, hgap43a, hdelta1, hgap01a, ht4b, hgap03a, hgap43b, hgap00b, hc34b, ht0a]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    linarith only [hgap41a, hdelta1, hc01b, ht12, hgap41b, htr234b, htr014c, hgap42b, hgap42a, hc23a]
              ·
                have hgap10a : (1 : ℝ) ≤ s10 := by exact_mod_cast hpositive10
                rcases hbridge41 with ⟨hzero41, hgap41b⟩ | ⟨hpositive41, hgap41b, hgap41c⟩
                ·
                  have hgap41a : (s41 : ℝ) = 0 := by exact_mod_cast hzero41
                  rcases hbridge42 with ⟨hzero42, hgap42b⟩ | ⟨hpositive42, hgap42b, hgap42c⟩
                  ·
                    have hgap42a : (s42 : ℝ) = 0 := by exact_mod_cast hzero42
                    rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                    ·
                      have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                      rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                      ·
                        have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                        linarith only [hgap41a, hgap43a, hgap44a, hsum4, hgap40a, hgap42a]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [hsum4, hgap44b, hgap04a, ht0a, hgap00b, hgap41a, hgap02a, htr034a, hdelta1, hgap01a, ht4b, hgap42a, hgap43a, hsum0, hgap40a, hgap03a]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [hc34b, hgap43a, hgap01a, hgap04a, hsum0, hgap00b, htr034b, hgap02a, ht4b, hdelta1, hgap43b, hgap03a, ht0a]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                    ·
                      have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                      rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                      ·
                        have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                        linarith only [hdelta1, hgap10a, htr012c, htr134b, hgap40a, hc01b, hgap41a, hgap43a, hsum4, hgap42b, htr024c, hgap44a, hgap10b]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [hgap01a, ht4b, hgap04a, hgap02a, hgap44b, htr034a, hgap03a, hdelta1, hgap44a, ht0a, hsum0, hgap00b]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [hsum0, hgap43b, hgap43a, hc34b, ht4b, hdelta1, hgap03a, ht0a, hgap02a, hgap04a, htr034b, hgap00b, hgap01a]
                ·
                  have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                  rcases hbridge42 with ⟨hzero42, hgap42b⟩ | ⟨hpositive42, hgap42b, hgap42c⟩
                  ·
                    have hgap42a : (s42 : ℝ) = 0 := by exact_mod_cast hzero42
                    rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                    ·
                      have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                      rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                      ·
                        have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                        linarith only [hdelta1, hc01b, hgap43a, hgap44a, hgap42a, hgap41b, ht12, htr014a, hgap40a, hc23a, htr234b, hsum4]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [ht12, htr034a, hgap03a, ht4b, htr012a, htr234b, hdelta1, hc01b, hgap02a, hgap42a, hgap40a, htr124c, ht0a, hsum4, hgap00b, hsum0, hgap04a, hgap43a, hc23a, hgap01a, hgap41b, hgap44b]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [hgap04a, hsum0, ht4b, hdelta1, hgap01a, hgap43b, hgap00b, hgap43a, ht0a, hc34b, hgap02a, htr034b, hgap03a]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    linarith only [htr014c, hc23a, hdelta1, hgap42a, hc01b, hgap41b, hgap42b, hgap41a, ht12, htr234b]
            ·
              have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
              rcases hbridge10 with ⟨hzero10, hgap10b⟩ | ⟨hpositive10, hgap10b, hgap10c⟩
              ·
                have hgap10a : (s10 : ℝ) = 0 := by exact_mod_cast hzero10
                rcases hbridge11 with ⟨hzero11, hgap11b⟩ | ⟨hpositive11, hgap11b, hgap11c⟩
                ·
                  have hgap11a : (s11 : ℝ) = 0 := by exact_mod_cast hzero11
                  rcases hbridge41 with ⟨hzero41, hgap41b⟩ | ⟨hpositive41, hgap41b, hgap41c⟩
                  ·
                    have hgap41a : (s41 : ℝ) = 0 := by exact_mod_cast hzero41
                    rcases hbridge12 with ⟨hzero12, hgap12b⟩ | ⟨hpositive12, hgap12b, hgap12c⟩
                    ·
                      have hgap12a : (s12 : ℝ) = 0 := by exact_mod_cast hzero12
                      rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
                      ·
                        have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
                        rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
                        ·
                          have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                          linarith only [hgap12a, hsum1, hgap13a, hgap10a, hgap11a, hgap14a]
                        ·
                          have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                          linarith only [hsum1, hgap04a, htr124a, hgap13a, hgap01a, hgap40a, hgap40b, hgap02a, hgap12a, hc34b, hgap10a, htr012a, htr034a, ht1b, hsum0, ht0a, hgap11a, hgap00b, hgap14b, hdelta1, hgap03a]
                      ·
                        have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
                        linarith only [hdelta1, ht34, hgap40a, hgap40b, hc01b, hgap13a, hgap13b, htr124a, ht12, ht23]
                    ·
                      have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
                      linarith only [htr012a, ht34, hdelta1, ht23, hc01b, hgap40b, hgap40a, ht12, htr124b, hgap12a, hgap12b]
                  ·
                    have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                    linarith only [hc01b, hgap41b, ht12, hgap41a, htr014a, hdelta1, hgap40a, ht34, ht23, hgap40b]
                ·
                  have hgap11a : (1 : ℝ) ≤ s11 := by exact_mod_cast hpositive11
                  rcases hbridge41 with ⟨hzero41, hgap41b⟩ | ⟨hpositive41, hgap41b, hgap41c⟩
                  ·
                    have hgap41a : (s41 : ℝ) = 0 := by exact_mod_cast hzero41
                    rcases hbridge42 with ⟨hzero42, hgap42b⟩ | ⟨hpositive42, hgap42b, hgap42c⟩
                    ·
                      have hgap42a : (s42 : ℝ) = 0 := by exact_mod_cast hzero42
                      rcases hbridge12 with ⟨hzero12, hgap12b⟩ | ⟨hpositive12, hgap12b, hgap12c⟩
                      ·
                        have hgap12a : (s12 : ℝ) = 0 := by exact_mod_cast hzero12
                        rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                        ·
                          have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                          rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                          ·
                            have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                            linarith only [hdelta1, hgap42a, hgap44a, hgap43a, hgap40b, ht34, hc12b, hsum4, ht23, htr124a, hgap41a]
                          ·
                            have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                            linarith only [hgap44b, ht0a, hgap03a, hdelta1, hgap04a, hgap44a, hsum0, hgap02a, htr034a, ht4b, hgap00b, hgap01a]
                        ·
                          have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                          linarith only [htr034b, hdelta1, hgap04a, hsum0, hgap03a, hgap01a, hc34b, hgap02a, ht0a, hgap00b, ht4b, hgap43b, hgap43a]
                      ·
                        have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
                        linarith only [hdelta1, htr012a, hgap11a, hgap12a, hgap11b, htr123b, hc01b, ht12, hgap12b, hc23a]
                    ·
                      have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                      linarith only [hc23a, hgap42a, hc01b, htr123b, hdelta1, htr014c, ht12, hgap11b, hgap11a, hgap42b]
                  ·
                    have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                    linarith only [ht12, ht34, htr014a, hc01b, hgap40a, hgap41a, hgap41b, hdelta1, hgap40b, ht23]
              ·
                have hgap10a : (1 : ℝ) ≤ s10 := by exact_mod_cast hpositive10
                rcases hbridge41 with ⟨hzero41, hgap41b⟩ | ⟨hpositive41, hgap41b, hgap41c⟩
                ·
                  have hgap41a : (s41 : ℝ) = 0 := by exact_mod_cast hzero41
                  rcases hbridge11 with ⟨hzero11, hgap11b⟩ | ⟨hpositive11, hgap11b, hgap11c⟩
                  ·
                    have hgap11a : (s11 : ℝ) = 0 := by exact_mod_cast hzero11
                    rcases hbridge42 with ⟨hzero42, hgap42b⟩ | ⟨hpositive42, hgap42b, hgap42c⟩
                    ·
                      have hgap42a : (s42 : ℝ) = 0 := by exact_mod_cast hzero42
                      rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                      ·
                        have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                        rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
                        ·
                          have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                          rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                          ·
                            have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                            linarith only [ht23, hdelta1, hgap43a, ht34, hgap41a, htr124a, hgap42a, hsum4, hgap40b, hgap44a, hc12b]
                          ·
                            have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                            linarith only [ht0a, hgap00b, hgap44a, ht4b, hgap04a, htr034a, hdelta1, hgap02a, hgap03a, hgap44b, hsum0, hgap01a]
                        ·
                          have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                          linarith only [hgap40b, htr012a, hgap40a, hgap14b, ht23, htr124a, ht34, hgap14a, ht12, hdelta1]
                      ·
                        have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                        linarith only [hc34b, hgap43b, htr034b, hsum0, hdelta1, hgap01a, ht4b, hgap43a, hgap04a, hgap02a, hgap03a, hgap00b, ht0a]
                    ·
                      have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                      rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                      ·
                        have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                        rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                        ·
                          have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                          linarith only [hc02b, hdelta1, htr024c, hsum4, htr124b, hgap43a, hgap41a, hgap44a, hgap40b, ht23, hgap42b, ht34]
                        ·
                          have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                          linarith only [hgap04a, hdelta1, ht0a, hgap44b, hsum0, ht4b, hgap01a, hgap44a, hgap00b, hgap03a, hgap02a, htr034a]
                      ·
                        have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                        linarith only [hgap01a, hgap03a, htr034b, ht0a, hsum0, ht4b, hgap43a, hgap43b, hgap00b, hgap02a, hdelta1, hc34b, hgap04a]
                  ·
                    have hgap11a : (1 : ℝ) ≤ s11 := by exact_mod_cast hpositive11
                    linarith only [hgap11b, hc01b, hdelta1, hgap11a, hgap10a, htr014a, hgap10b]
                ·
                  have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                  linarith only [hdelta1, ht34, hgap40b, hgap41a, ht12, hgap40a, hc01b, hgap41b, ht23, htr014a]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            rcases hbridge10 with ⟨hzero10, hgap10b⟩ | ⟨hpositive10, hgap10b, hgap10c⟩
            ·
              have hgap10a : (s10 : ℝ) = 0 := by exact_mod_cast hzero10
              rcases hbridge11 with ⟨hzero11, hgap11b⟩ | ⟨hpositive11, hgap11b, hgap11c⟩
              ·
                have hgap11a : (s11 : ℝ) = 0 := by exact_mod_cast hzero11
                rcases hbridge12 with ⟨hzero12, hgap12b⟩ | ⟨hpositive12, hgap12b, hgap12c⟩
                ·
                  have hgap12a : (s12 : ℝ) = 0 := by exact_mod_cast hzero12
                  rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
                  ·
                    have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
                    rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
                    ·
                      have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                      linarith only [hgap11a, hgap10a, hsum1, hgap13a, hgap12a, hgap14a]
                    ·
                      have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                      linarith only [hgap12a, htr012a, hgap14b, htr124a, ht12, hc23a, hgap11a, htr234b, hgap10a, hsum1, hgap13a, hdelta1]
                  ·
                    have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
                    linarith only [hgap04a, hdelta1, ht01, htr234b, ht12, htr124a, hgap04b, hgap13b, hgap13a, hc23a]
                ·
                  have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
                  linarith only [htr123b, htr134b, hgap04a, htr012a, ht12, hgap12b, ht01, hgap12a, hgap04b, hc23a, hdelta1]
              ·
                have hgap11a : (1 : ℝ) ≤ s11 := by exact_mod_cast hpositive11
                linarith only [hc23a, hgap04b, hgap04a, ht01, htr012a, ht12, hgap11a, htr123b, hdelta1, hgap11b, htr124c]
            ·
              have hgap10a : (1 : ℝ) ≤ s10 := by exact_mod_cast hpositive10
              rcases hbridge40 with ⟨hzero40, hgap40b⟩ | ⟨hpositive40, hgap40b, hgap40c⟩
              ·
                have hgap40a : (s40 : ℝ) = 0 := by exact_mod_cast hzero40
                rcases hbridge41 with ⟨hzero41, hgap41b⟩ | ⟨hpositive41, hgap41b, hgap41c⟩
                ·
                  have hgap41a : (s41 : ℝ) = 0 := by exact_mod_cast hzero41
                  rcases hbridge42 with ⟨hzero42, hgap42b⟩ | ⟨hpositive42, hgap42b, hgap42c⟩
                  ·
                    have hgap42a : (s42 : ℝ) = 0 := by exact_mod_cast hzero42
                    rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                    ·
                      have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                      rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                      ·
                        have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                        linarith only [hgap44a, hsum4, hgap41a, hgap43a, hgap42a, hgap40a]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [ht01, hgap42a, ht12, hdelta1, hgap00b, hc23a, hgap43a, hgap01a, hgap40a, htr034a, hsum4, hsum0, hgap41a, hgap44b, htr124a, ht4b, hgap02a, htr234b, hgap04b, ht0a, htr012a, hgap03a]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                      ·
                        have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                        linarith only [htr234b, ht4b, hgap44a, hgap42a, hgap01a, htr034b, hsum0, ht01, hgap41a, hgap02a, hdelta1, ht0a, hsum4, hgap00b, htr012a, htr124a, hc23a, hgap40a, hgap04b, ht12, hc34b, hgap43b, hgap03a]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [ht01, htr124a, hdelta1, hgap44b, ht12, hc23a, hgap01a, htr012a, hgap00b, hgap41a, htr034b, hgap02a, hgap03a, hgap42a, hgap40a, htr234b, hsum0, hgap43b, ht4b, hgap04b, hsum4, ht0a]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    linarith only [hgap10a, hdelta1, hgap04b, ht01, hgap42a, hgap04a, htr012c, hgap42b, htr134b, htr024c, hgap10b]
                ·
                  have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                  linarith only [hgap04b, ht12, htr012a, htr124c, hc23a, hgap04a, htr234b, hdelta1, hgap41b, hgap41a, ht01]
              ·
                have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
                linarith only [hdelta1, htr012a, ht34, ht12, htr124a, hgap40b, ht01, hgap40a, hgap04a, hgap04b, ht23]
        ·
          have hgap03a : (1 : ℝ) ≤ s03 := by exact_mod_cast hpositive03
          rcases hbridge40 with ⟨hzero40, hgap40b⟩ | ⟨hpositive40, hgap40b, hgap40c⟩
          ·
            have hgap40a : (s40 : ℝ) = 0 := by exact_mod_cast hzero40
            rcases hbridge41 with ⟨hzero41, hgap41b⟩ | ⟨hpositive41, hgap41b, hgap41c⟩
            ·
              have hgap41a : (s41 : ℝ) = 0 := by exact_mod_cast hzero41
              rcases hbridge42 with ⟨hzero42, hgap42b⟩ | ⟨hpositive42, hgap42b, hgap42c⟩
              ·
                have hgap42a : (s42 : ℝ) = 0 := by exact_mod_cast hzero42
                rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                ·
                  have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                  rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                  ·
                    have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                    linarith only [hgap43a, hgap42a, hgap44a, hgap41a, hgap40a, hsum4]
                  ·
                    have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                    linarith only [hgap43a, hgap42a, htr034a, hdelta1, hgap44b, hgap00a, ht4b, hgap00b, hgap40a, ht0a, hgap41a, hsum4]
                ·
                  have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                  rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                  ·
                    have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                    linarith only [hsum4, hgap40a, hgap00a, ht0a, hc34b, hgap44a, ht4b, hgap00b, htr034b, hgap41a, hgap42a, hdelta1, hgap43b]
                  ·
                    have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                    linarith only [hsum4, hgap41a, ht4b, hgap43b, htr034b, hdelta1, hgap00b, hgap00a, ht0a, hgap40a, hgap44b, hgap42a]
              ·
                have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                linarith only [hc01b, hgap03a, hgap03b, htr134b, hdelta1, hgap42a, hc13a, htr024c, hgap42b]
            ·
              have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
              linarith only [hgap41a, hc23a, hgap03b, htr014b, htr024c, hdelta1, ht12, hgap41b, htr234b, hc01b, hgap03a]
          ·
            have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
            linarith only [hdelta1, hgap03a, ht23, hgap40a, htr124a, ht34, hgap40b, htr012b, hgap03b, ht12, hc01b]
      ·
        have hgap02a : (1 : ℝ) ≤ s02 := by exact_mod_cast hpositive02
        rcases hbridge03 with ⟨hzero03, hgap03b⟩ | ⟨hpositive03, hgap03b, hgap03c⟩
        ·
          have hgap03a : (s03 : ℝ) = 0 := by exact_mod_cast hzero03
          rcases hbridge04 with ⟨hzero04, hgap04b⟩ | ⟨hpositive04, hgap04b, hgap04c⟩
          ·
            have hgap04a : (s04 : ℝ) = 0 := by exact_mod_cast hzero04
            rcases hbridge10 with ⟨hzero10, hgap10b⟩ | ⟨hpositive10, hgap10b, hgap10c⟩
            ·
              have hgap10a : (s10 : ℝ) = 0 := by exact_mod_cast hzero10
              rcases hbridge11 with ⟨hzero11, hgap11b⟩ | ⟨hpositive11, hgap11b, hgap11c⟩
              ·
                have hgap11a : (s11 : ℝ) = 0 := by exact_mod_cast hzero11
                rcases hbridge12 with ⟨hzero12, hgap12b⟩ | ⟨hpositive12, hgap12b, hgap12c⟩
                ·
                  have hgap12a : (s12 : ℝ) = 0 := by exact_mod_cast hzero12
                  rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
                  ·
                    have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
                    rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
                    ·
                      have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                      linarith only [hgap11a, hgap14a, hgap10a, hsum1, hgap13a, hgap12a]
                    ·
                      have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                      linarith only [hgap02b, ht1b, ht0a, hgap03a, hgap11a, hgap04a, hgap00b, hgap13a, hgap10a, hdelta1, hgap01a, htr034b, hsum0, hgap14b, hgap12a, hsum1, htr012c]
                  ·
                    have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
                    rcases hbridge40 with ⟨hzero40, hgap40b⟩ | ⟨hpositive40, hgap40b, hgap40c⟩
                    ·
                      have hgap40a : (s40 : ℝ) = 0 := by exact_mod_cast hzero40
                      rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
                      ·
                        have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                        linarith only [hgap11a, hgap13b, htr124a, hgap10a, ht12, hdelta1, hsum1, hc01b, htr234b, hgap12a, hgap14a, hc23a]
                      ·
                        have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                        linarith only [hgap14a, hgap00b, hgap04a, ht1b, htr034b, ht0a, hgap01a, hdelta1, htr012c, hgap14b, hgap02b, hsum0, hgap03a]
                    ·
                      have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
                      linarith only [hdelta1, ht12, hgap13a, ht34, hgap40b, ht23, hc01b, hgap13b, hgap40a, htr124a]
                ·
                  have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
                  rcases hbridge40 with ⟨hzero40, hgap40b⟩ | ⟨hpositive40, hgap40b, hgap40c⟩
                  ·
                    have hgap40a : (s40 : ℝ) = 0 := by exact_mod_cast hzero40
                    rcases hbridge41 with ⟨hzero41, hgap41b⟩ | ⟨hpositive41, hgap41b, hgap41c⟩
                    ·
                      have hgap41a : (s41 : ℝ) = 0 := by exact_mod_cast hzero41
                      rcases hbridge42 with ⟨hzero42, hgap42b⟩ | ⟨hpositive42, hgap42b, hgap42c⟩
                      ·
                        have hgap42a : (s42 : ℝ) = 0 := by exact_mod_cast hzero42
                        rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                        ·
                          have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                          rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                          ·
                            have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                            linarith only [hgap44a, hsum4, hgap40a, hgap43a, hgap42a, hgap41a]
                          ·
                            have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                            linarith only [hgap43a, hdelta1, hgap41a, hgap00a, hgap40a, hsum4, ht0a, hgap42a, htr034a, ht4b, hgap00b, hgap44b]
                        ·
                          have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                          rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                          ·
                            have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                            linarith only [hc34b, hgap44a, hgap41a, hgap40a, hgap00a, hdelta1, htr034b, hgap42a, hgap00b, ht4b, hsum4, hgap43b, ht0a]
                          ·
                            have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                            linarith only [hdelta1, htr034b, hgap00a, hgap00b, hgap44b, hgap41a, hgap43b, hsum4, hgap40a, ht4b, hgap42a, ht0a]
                      ·
                        have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                        linarith only [hdelta1, hc23a, htr123b, hgap02a, ht12, hc01b, htr134b, hgap42a, htr012c, hgap42b, hgap02b]
                    ·
                      have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                      linarith only [hgap12a, hc23a, hc12b, hdelta1, htr234b, hgap41b, hgap12b, hgap41a]
                  ·
                    have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
                    linarith only [hgap40a, ht23, hgap12b, hgap40b, hdelta1, hgap12a, htr012a, hc01b, ht12, ht34, htr124b]
              ·
                have hgap11a : (1 : ℝ) ≤ s11 := by exact_mod_cast hpositive11
                linarith only [hgap02b, hgap02a, htr012c, ht12, hgap11a, hgap11b, htr123b, hc23a, hc01b, htr014b, hdelta1]
            ·
              have hgap10a : (1 : ℝ) ≤ s10 := by exact_mod_cast hpositive10
              rcases hbridge11 with ⟨hzero11, hgap11b⟩ | ⟨hpositive11, hgap11b, hgap11c⟩
              ·
                have hgap11a : (s11 : ℝ) = 0 := by exact_mod_cast hzero11
                rcases hbridge12 with ⟨hzero12, hgap12b⟩ | ⟨hpositive12, hgap12b, hgap12c⟩
                ·
                  have hgap12a : (s12 : ℝ) = 0 := by exact_mod_cast hzero12
                  rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
                  ·
                    have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
                    rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
                    ·
                      have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                      linarith only [hgap12a, hsum1, hdelta1, htr012c, hgap11a, htr034b, hgap10b, htr013b, hgap13a, hgap02b, hgap14a, hgap02a, hc01b]
                    ·
                      have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                      linarith only [hgap01a, hsum0, hgap14b, htr012c, hgap03a, hgap14a, hgap00b, hgap02b, hdelta1, htr034b, hgap04a, ht1b, ht0a]
                  ·
                    have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
                    rcases hbridge40 with ⟨hzero40, hgap40b⟩ | ⟨hpositive40, hgap40b, hgap40c⟩
                    ·
                      have hgap40a : (s40 : ℝ) = 0 := by exact_mod_cast hzero40
                      rcases hbridge33 with ⟨hzero33, hgap33b⟩ | ⟨hpositive33, hgap33b, hgap33c⟩
                      ·
                        have hgap33a : (s33 : ℝ) = 0 := by exact_mod_cast hzero33
                        rcases hbridge41 with ⟨hzero41, hgap41b⟩ | ⟨hpositive41, hgap41b, hgap41c⟩
                        ·
                          have hgap41a : (s41 : ℝ) = 0 := by exact_mod_cast hzero41
                          rcases hbridge42 with ⟨hzero42, hgap42b⟩ | ⟨hpositive42, hgap42b, hgap42c⟩
                          ·
                            have hgap42a : (s42 : ℝ) = 0 := by exact_mod_cast hzero42
                            rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                            ·
                              have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                              rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                              ·
                                have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                                linarith only [hgap42a, hgap41a, hgap43a, hsum4, hgap44a, hgap40a]
                              ·
                                have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                                linarith only [hgap44b, hsum4, ht4b, hgap10a, hgap04a, hgap10b, hgap43a, htr034b, hgap41a, hsum0, hgap40a, htr013b, hgap03a, hgap42a, hdelta1, hgap02b, hgap00b, htr034a, ht0a, htr012c, hgap01a, hc01b]
                            ·
                              have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                              linarith only [htr034b, hgap43b, hgap33b, hgap43a]
                          ·
                            have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                            linarith only [hgap02b, hgap42b, hgap04a, hdelta1, hsum0, htr134b, hgap10b, hc01b, htr012c, hgap42a, hgap10a, hscore00b, hgap01a, hgap03a]
                        ·
                          have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                          linarith only [hgap02b, hgap41a, hdelta1, hgap41b, htr234b, htr012c, hgap02a, hc23a, htr014b, ht12, hc01b]
                      ·
                        have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                        rcases hbridge41 with ⟨hzero41, hgap41b⟩ | ⟨hpositive41, hgap41b, hgap41c⟩
                        ·
                          have hgap41a : (s41 : ℝ) = 0 := by exact_mod_cast hzero41
                          rcases hbridge42 with ⟨hzero42, hgap42b⟩ | ⟨hpositive42, hgap42b, hgap42c⟩
                          ·
                            have hgap42a : (s42 : ℝ) = 0 := by exact_mod_cast hzero42
                            rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                            ·
                              have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                              rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                              ·
                                have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                                linarith only [hgap44a, hgap43a, hgap42a, hsum4, hgap40a, hgap41a]
                              ·
                                have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                                linarith only [hgap42a, hgap03a, ht0a, hgap44b, hgap10b, htr012c, htr034b, hsum4, htr013b, hgap41a, hgap10a, hgap00b, hgap04a, hgap43a, hgap33a, hc01b, ht4b, hgap40a, hdelta1, hgap33b, hgap02b, hsum0, hgap01a]
                            ·
                              have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                              rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                              ·
                                have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                                linarith only [htr012c, hdelta1, hgap02b, hgap40a, ht4b, hsum0, hgap00b, hsum4, hgap10b, hc01b, htr034b, hgap10a, hc34b, hgap03a, hgap41a, ht0a, hgap42a, hgap44a, hgap01a, hgap43b, hgap04a, htr013b]
                              ·
                                have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                                linarith only [ht0a, hgap40a, hdelta1, htr034b, hgap00b, hgap10a, hgap42a, hgap41a, hgap01a, htr012c, hgap03a, htr013b, ht4b, hgap04a, hgap10b, hgap43b, hsum4, hsum0, hc01b, hgap02b, hgap44b]
                          ·
                            have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                            linarith only [hdelta1, ht0a, hgap02b, hgap01a, htr134b, hgap03a, hgap04a, htr012c, hgap33a, hc01b, hc34b, hgap10a, hsum0, hgap10b, ht4b, hgap33b, hgap42a, hgap00b, hgap42b]
                        ·
                          have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                          linarith only [htr234b, hc01b, hgap02a, hgap41a, hdelta1, ht12, hgap02b, hgap41b, htr014b, htr012c, hc23a]
                    ·
                      have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
                      linarith only [hgap13a, htr124a, hgap13b, ht12, ht23, hdelta1, hc01b, hgap40b, hgap40a, ht34]
                ·
                  have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
                  linarith only [hgap12a, hc01b, hgap12b, htr012a, htr134b, hgap10b, hgap10a, hdelta1]
              ·
                have hgap11a : (1 : ℝ) ≤ s11 := by exact_mod_cast hpositive11
                linarith only [htr014a, hc01b, hdelta1, hgap10a, hgap11a, hgap10b, hgap11b]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            linarith only [hgap02a, hgap02b, hgap04b, hdelta1, hgap04a, htr034b, hgap00a, htr012c, hgap00b]
        ·
          have hgap03a : (1 : ℝ) ≤ s03 := by exact_mod_cast hpositive03
          linarith only [hgap02b, hgap00a, htr034b, hgap03b, hgap02a, ht0a, hgap03a, ht34, ht12, ht23, ht4b, hc01b, hdelta1, hgap00b]
    ·
      have hgap01a : (1 : ℝ) ≤ s01 := by exact_mod_cast hpositive01
      rcases hbridge10 with ⟨hzero10, hgap10b⟩ | ⟨hpositive10, hgap10b, hgap10c⟩
      ·
        have hgap10a : (s10 : ℝ) = 0 := by exact_mod_cast hzero10
        rcases hbridge11 with ⟨hzero11, hgap11b⟩ | ⟨hpositive11, hgap11b, hgap11c⟩
        ·
          have hgap11a : (s11 : ℝ) = 0 := by exact_mod_cast hzero11
          rcases hbridge02 with ⟨hzero02, hgap02b⟩ | ⟨hpositive02, hgap02b, hgap02c⟩
          ·
            have hgap02a : (s02 : ℝ) = 0 := by exact_mod_cast hzero02
            rcases hbridge12 with ⟨hzero12, hgap12b⟩ | ⟨hpositive12, hgap12b, hgap12c⟩
            ·
              have hgap12a : (s12 : ℝ) = 0 := by exact_mod_cast hzero12
              rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
              ·
                have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
                rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
                ·
                  have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                  linarith only [hgap10a, hgap11a, hgap13a, hsum1, hgap14a, hgap12a]
                ·
                  have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                  linarith only [hgap12a, hgap10a, hgap13a, hsum1, hgap00a, hgap11a, hgap01b, ht34, ht12, hgap00b, hgap14b, ht23, ht4b, htr012c, ht0a, hgap01a, htr024c, hdelta1]
              ·
                have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
                rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
                ·
                  have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                  linarith only [hc01b, hgap13b, hdelta1, htr234b, hsum1, hgap12a, hgap14a, hgap11a, ht12, hc23a, htr124a, hgap10a]
                ·
                  have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                  linarith only [hgap14b, hgap14a, hc23a, htr124a, ht12, htr234b, hdelta1, hgap13a, hgap13b]
            ·
              have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
              rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
              ·
                have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
                rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
                ·
                  have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                  linarith only [hdelta1, htr012a, hc01b, hc13a, hgap14a, hsum1, hgap10a, hgap13a, hgap11a, hgap12b, htr134b]
                ·
                  have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                  linarith only [hgap12a, hgap12b, htr134b, hgap14a, hdelta1, hc13a, htr012a, hgap14b]
              ·
                have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
                linarith only [hgap12a, hdelta1, hgap13a, hgap12b, htr134b, hc01b, hgap13b, hc13a]
          ·
            have hgap02a : (1 : ℝ) ≤ s02 := by exact_mod_cast hpositive02
            linarith only [ht23, ht12, hgap02b, hc01b, hgap00a, ht0a, hgap01b, hgap02a, ht34, hdelta1, hgap00b, hgap01a, ht4b, htr012c]
        ·
          have hgap11a : (1 : ℝ) ≤ s11 := by exact_mod_cast hpositive11
          rcases hbridge12 with ⟨hzero12, hgap12b⟩ | ⟨hpositive12, hgap12b, hgap12c⟩
          ·
            have hgap12a : (s12 : ℝ) = 0 := by exact_mod_cast hzero12
            rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
            ·
              have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
              rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
              ·
                have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                linarith only [hsum1, hgap13a, hgap14a, hgap12a, hdelta1, htr014a, hc13a, hgap10a, hgap11b, hc01b]
              ·
                have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                linarith only [hgap11b, hgap14a, hgap14b, htr012a, hdelta1, hgap11a, hc13a, htr124c]
            ·
              have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
              linarith only [htr124c, hc01b, hdelta1, hgap11b, hc13a, hgap13a, hgap11a, hgap13b]
          ·
            have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
            linarith only [hgap11b, hgap11a, hdelta1, hgap12b, hc01b, hc13a, htr012a, hgap12a]
      ·
        have hgap10a : (1 : ℝ) ≤ s10 := by exact_mod_cast hpositive10
        rcases hbridge11 with ⟨hzero11, hgap11b⟩ | ⟨hpositive11, hgap11b, hgap11c⟩
        ·
          have hgap11a : (s11 : ℝ) = 0 := by exact_mod_cast hzero11
          rcases hbridge12 with ⟨hzero12, hgap12b⟩ | ⟨hpositive12, hgap12b, hgap12c⟩
          ·
            have hgap12a : (s12 : ℝ) = 0 := by exact_mod_cast hzero12
            rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
            ·
              have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
              rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
              ·
                have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                linarith only [hgap14a, hgap13a, htr012c, hc01b, hsum1, hgap01b, htr013b, hgap01a, hgap12a, hgap11a, hgap10b, hdelta1, htr024c]
              ·
                have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                linarith only [hdelta1, hgap10b, hgap10a, htr013b, hgap14a, hgap01b, htr012c, hgap14b, htr024c, hgap01a]
            ·
              have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
              rcases hbridge02 with ⟨hzero02, hgap02b⟩ | ⟨hpositive02, hgap02b, hgap02c⟩
              ·
                have hgap02a : (s02 : ℝ) = 0 := by exact_mod_cast hzero02
                rcases hbridge40 with ⟨hzero40, hgap40b⟩ | ⟨hpositive40, hgap40b, hgap40c⟩
                ·
                  have hgap40a : (s40 : ℝ) = 0 := by exact_mod_cast hzero40
                  rcases hbridge03 with ⟨hzero03, hgap03b⟩ | ⟨hpositive03, hgap03b, hgap03c⟩
                  ·
                    have hgap03a : (s03 : ℝ) = 0 := by exact_mod_cast hzero03
                    rcases hbridge41 with ⟨hzero41, hgap41b⟩ | ⟨hpositive41, hgap41b, hgap41c⟩
                    ·
                      have hgap41a : (s41 : ℝ) = 0 := by exact_mod_cast hzero41
                      rcases hbridge42 with ⟨hzero42, hgap42b⟩ | ⟨hpositive42, hgap42b, hgap42c⟩
                      ·
                        have hgap42a : (s42 : ℝ) = 0 := by exact_mod_cast hzero42
                        rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                        ·
                          have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                          rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                          ·
                            have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                            linarith only [hgap43a, hgap41a, hgap42a, hgap44a, hgap40a, hsum4]
                          ·
                            have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                            linarith only [hgap43a, hsum4, hgap41a, htr034c, ht0a, ht4b, hgap10b, htr013b, hdelta1, hgap44b, hgap01a, hgap10a, hgap01b, hgap42a, ht01, hgap40a]
                        ·
                          have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                          linarith only [hgap43b, ht0a, hgap43a, hgap10a, htr013b, ht4b, hgap10b, hgap01a, ht01, hgap01b, hc34b, hdelta1]
                      ·
                        have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                        rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                        ·
                          have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                          rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                          ·
                            have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                            linarith only [hc01b, hgap10a, hgap43a, hgap44a, htr024c, htr012c, hgap40a, hgap42b, hgap10b, hdelta1, htr134b, hsum4, hgap41a]
                          ·
                            have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                            linarith only [ht4b, hgap10b, hgap41a, hgap10a, hgap43a, htr134b, ht01, hgap44b, hsum4, ht0a, hgap40a, hdelta1, hgap42b, htr034c]
                        ·
                          have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                          linarith only [hgap43a, ht0a, hgap10a, hgap01b, ht4b, hgap01a, hdelta1, hc34b, hgap43b, ht01, htr013b, hgap10b]
                    ·
                      have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                      linarith only [hc01b, hgap41a, ht12, hdelta1, htr124c, hgap13a, hc23a, htr234b, hgap13b, hgap41b]
                  ·
                    have hgap03a : (1 : ℝ) ≤ s03 := by exact_mod_cast hpositive03
                    linarith only [htr024c, hc01b, hdelta1, hgap01a, hgap10b, hgap10a, htr013b, hgap03a, hgap01b, hgap03b]
                ·
                  have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
                  linarith only [ht34, hgap40a, hgap13b, hgap40b, ht23, hc01b, hgap13a, htr124a, ht12, hdelta1]
              ·
                have hgap02a : (1 : ℝ) ≤ s02 := by exact_mod_cast hpositive02
                linarith only [ht01, hgap02a, hgap02b, ht34, ht0a, hgap10b, ht4b, hgap01a, ht23, hgap01b, htr013b, hdelta1, hgap10a, hc02b]
          ·
            have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
            linarith only [hdelta1, hgap12b, htr012a, htr134b, hgap10b, hc01b, hgap10a, hgap12a]
        ·
          have hgap11a : (1 : ℝ) ≤ s11 := by exact_mod_cast hpositive11
          linarith only [hgap11a, hgap10b, hgap10a, htr014a, hdelta1, hgap11b, hc01b]

#print axioms n5_between_mask223
end Jsp404.SixExactFloorKernel
