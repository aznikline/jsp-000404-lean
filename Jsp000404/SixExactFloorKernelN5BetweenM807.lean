import Jsp000404.SixExactFloorKernelPrimitives

/-! Representative exact-score certificate. A fixed orientation is an explicit
hypothesis only for this probe; public wrappers must split every triangle arm. -/
namespace Jsp404.SixExactFloorKernel

set_option maxHeartbeats 16000000 in
theorem n5_between_mask807 (M : SixModelCompression.ModelSix 5)
    (hhigh : (1/2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    (htri012 : M.d 1 2+1 ≤ M.d 0 1 ∧ M.d 1 2 < M.d 0 2 ∧ M.d 0 2 < M.d 0 1)
    (htri013 : M.d 1 3+1 ≤ M.d 0 1 ∧ M.d 1 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 1)
    (htri014 : M.d 1 4+1 ≤ M.d 0 1 ∧ M.d 1 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 1)
    (htri023 : M.d 0 2+1 ≤ M.d 2 3 ∧ M.d 0 2 < M.d 0 3 ∧ M.d 0 3 < M.d 2 3)
    (htri024 : M.d 0 2+1 ≤ M.d 2 4 ∧ M.d 0 2 < M.d 0 4 ∧ M.d 0 4 < M.d 2 4)
    (htri034 : M.d 3 4+1 ≤ M.d 0 3 ∧ M.d 3 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 3)
    (htri123 : M.d 1 2+1 ≤ M.d 2 3 ∧ M.d 1 2 < M.d 1 3 ∧ M.d 1 3 < M.d 2 3)
    (htri124 : M.d 1 2+1 ≤ M.d 2 4 ∧ M.d 1 2 < M.d 1 4 ∧ M.d 1 4 < M.d 2 4)
    (htri134 : M.d 3 4+1 ≤ M.d 1 3 ∧ M.d 3 4 < M.d 1 4 ∧ M.d 1 4 < M.d 1 3)
    (htri234 : M.d 3 4+1 ≤ M.d 2 3 ∧ M.d 3 4 < M.d 2 4 ∧ M.d 2 4 < M.d 2 3)
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
  have hsort0 : ([M.d 0 2, M.d 0 4, M.d 0 3, M.d 0 1] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp0 := M.row_perm 0
  have he0 : (((List.finRange 5).erase (0 : Fin 5)).map (M.d 0)) = [M.d 0 1, M.d 0 2, M.d 0 3, M.d 0 4] := by
    norm_num [List.finRange, List.ofFn_succ]
  rw [he0] at hp0
  have hperm0 := hp0.trans (((((List.Perm.swap (M.d 0 2) (M.d 0 1) [M.d 0 3, M.d 0 4]).trans (((List.Perm.swap (M.d 0 4) (M.d 0 3) []).cons (M.d 0 1)).cons (M.d 0 2))).trans ((List.Perm.swap (M.d 0 4) (M.d 0 1) [M.d 0 3]).cons (M.d 0 2))).trans (((List.Perm.swap (M.d 0 3) (M.d 0 1) []).cons (M.d 0 4)).cons (M.d 0 2))))
  have hrow0 : M.rowxs 0 = [M.d 0 2, M.d 0 4, M.d 0 3, M.d 0 1] := hperm0.eq_of_pairwise' (M.row_sorted 0) hsort0
  have hrow_nonneg0 := SmallScoreGapBounds.model_gaps_nonneg M 0
  simp only [SmallScoreGapBounds.modelGaps, hrow0, StrongGapBudget.linearGaps] at hrow_nonneg0
  norm_num only [Nat.cast_ofNat] at hrow_nonneg0
  let s00 : ℕ := ⌊(M.d 0 2 - M.theta 0)⌋₊ - 1
  have hnonneg00 : 0 ≤ (M.d 0 2 - M.theta 0) := hrow_nonneg0 (M.d 0 2 - M.theta 0) (by simp)
  have hscore00a : (0 : ℝ) ≤ s00 := Nat.cast_nonneg s00
  have hbridge00 := score_gap_dichotomy (M.d 0 2 - M.theta 0) hnonneg00
  change (s00 = 0 ∧ (M.d 0 2 - M.theta 0) < 2) ∨ (1 ≤ s00 ∧ (s00 : ℝ)+1 ≤ (M.d 0 2 - M.theta 0) ∧ (M.d 0 2 - M.theta 0) < (s00 : ℝ)+2) at hbridge00
  let s01 : ℕ := ⌊(M.d 0 4 - M.d 0 2)⌋₊ - 1
  have hnonneg01 : 0 ≤ (M.d 0 4 - M.d 0 2) := hrow_nonneg0 (M.d 0 4 - M.d 0 2) (by simp)
  have hscore01a : (0 : ℝ) ≤ s01 := Nat.cast_nonneg s01
  have hbridge01 := score_gap_dichotomy (M.d 0 4 - M.d 0 2) hnonneg01
  change (s01 = 0 ∧ (M.d 0 4 - M.d 0 2) < 2) ∨ (1 ≤ s01 ∧ (s01 : ℝ)+1 ≤ (M.d 0 4 - M.d 0 2) ∧ (M.d 0 4 - M.d 0 2) < (s01 : ℝ)+2) at hbridge01
  let s02 : ℕ := ⌊(M.d 0 3 - M.d 0 4)⌋₊ - 1
  have hnonneg02 : 0 ≤ (M.d 0 3 - M.d 0 4) := hrow_nonneg0 (M.d 0 3 - M.d 0 4) (by simp)
  have hscore02a : (0 : ℝ) ≤ s02 := Nat.cast_nonneg s02
  have hbridge02 := score_gap_dichotomy (M.d 0 3 - M.d 0 4) hnonneg02
  change (s02 = 0 ∧ (M.d 0 3 - M.d 0 4) < 2) ∨ (1 ≤ s02 ∧ (s02 : ℝ)+1 ≤ (M.d 0 3 - M.d 0 4) ∧ (M.d 0 3 - M.d 0 4) < (s02 : ℝ)+2) at hbridge02
  let s03 : ℕ := ⌊(M.d 0 1 - M.d 0 3)⌋₊ - 1
  have hnonneg03 : 0 ≤ (M.d 0 1 - M.d 0 3) := hrow_nonneg0 (M.d 0 1 - M.d 0 3) (by simp)
  have hscore03a : (0 : ℝ) ≤ s03 := Nat.cast_nonneg s03
  have hbridge03 := score_gap_dichotomy (M.d 0 1 - M.d 0 3) hnonneg03
  change (s03 = 0 ∧ (M.d 0 1 - M.d 0 3) < 2) ∨ (1 ≤ s03 ∧ (s03 : ℝ)+1 ≤ (M.d 0 1 - M.d 0 3) ∧ (M.d 0 1 - M.d 0 3) < (s03 : ℝ)+2) at hbridge03
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
  have hsort1 : ([M.d 1 2, M.d 1 4, M.d 1 3, M.d 0 1] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp1 := M.row_perm 1
  have hcanon10 : M.d 1 0 = M.d 0 1 := M.symm 1 0 (by decide)
  have he1 : (((List.finRange 5).erase (1 : Fin 5)).map (M.d 1)) = [M.d 0 1, M.d 1 2, M.d 1 3, M.d 1 4] := by
    norm_num [List.finRange, List.ofFn_succ, hcanon10]
  rw [he1] at hp1
  have hperm1 := hp1.trans (((((List.Perm.swap (M.d 1 2) (M.d 0 1) [M.d 1 3, M.d 1 4]).trans (((List.Perm.swap (M.d 1 4) (M.d 1 3) []).cons (M.d 0 1)).cons (M.d 1 2))).trans ((List.Perm.swap (M.d 1 4) (M.d 0 1) [M.d 1 3]).cons (M.d 1 2))).trans (((List.Perm.swap (M.d 1 3) (M.d 0 1) []).cons (M.d 1 4)).cons (M.d 1 2))))
  have hrow1 : M.rowxs 1 = [M.d 1 2, M.d 1 4, M.d 1 3, M.d 0 1] := hperm1.eq_of_pairwise' (M.row_sorted 1) hsort1
  have hrow_nonneg1 := SmallScoreGapBounds.model_gaps_nonneg M 1
  simp only [SmallScoreGapBounds.modelGaps, hrow1, StrongGapBudget.linearGaps] at hrow_nonneg1
  norm_num only [Nat.cast_ofNat] at hrow_nonneg1
  let s10 : ℕ := ⌊(M.d 1 2 - M.theta 1)⌋₊ - 1
  have hnonneg10 : 0 ≤ (M.d 1 2 - M.theta 1) := hrow_nonneg1 (M.d 1 2 - M.theta 1) (by simp)
  have hscore10a : (0 : ℝ) ≤ s10 := Nat.cast_nonneg s10
  have hbridge10 := score_gap_dichotomy (M.d 1 2 - M.theta 1) hnonneg10
  change (s10 = 0 ∧ (M.d 1 2 - M.theta 1) < 2) ∨ (1 ≤ s10 ∧ (s10 : ℝ)+1 ≤ (M.d 1 2 - M.theta 1) ∧ (M.d 1 2 - M.theta 1) < (s10 : ℝ)+2) at hbridge10
  let s11 : ℕ := ⌊(M.d 1 4 - M.d 1 2)⌋₊ - 1
  have hnonneg11 : 0 ≤ (M.d 1 4 - M.d 1 2) := hrow_nonneg1 (M.d 1 4 - M.d 1 2) (by simp)
  have hscore11a : (0 : ℝ) ≤ s11 := Nat.cast_nonneg s11
  have hbridge11 := score_gap_dichotomy (M.d 1 4 - M.d 1 2) hnonneg11
  change (s11 = 0 ∧ (M.d 1 4 - M.d 1 2) < 2) ∨ (1 ≤ s11 ∧ (s11 : ℝ)+1 ≤ (M.d 1 4 - M.d 1 2) ∧ (M.d 1 4 - M.d 1 2) < (s11 : ℝ)+2) at hbridge11
  let s12 : ℕ := ⌊(M.d 1 3 - M.d 1 4)⌋₊ - 1
  have hnonneg12 : 0 ≤ (M.d 1 3 - M.d 1 4) := hrow_nonneg1 (M.d 1 3 - M.d 1 4) (by simp)
  have hscore12a : (0 : ℝ) ≤ s12 := Nat.cast_nonneg s12
  have hbridge12 := score_gap_dichotomy (M.d 1 3 - M.d 1 4) hnonneg12
  change (s12 = 0 ∧ (M.d 1 3 - M.d 1 4) < 2) ∨ (1 ≤ s12 ∧ (s12 : ℝ)+1 ≤ (M.d 1 3 - M.d 1 4) ∧ (M.d 1 3 - M.d 1 4) < (s12 : ℝ)+2) at hbridge12
  let s13 : ℕ := ⌊(M.d 0 1 - M.d 1 3)⌋₊ - 1
  have hnonneg13 : 0 ≤ (M.d 0 1 - M.d 1 3) := hrow_nonneg1 (M.d 0 1 - M.d 1 3) (by simp)
  have hscore13a : (0 : ℝ) ≤ s13 := Nat.cast_nonneg s13
  have hbridge13 := score_gap_dichotomy (M.d 0 1 - M.d 1 3) hnonneg13
  change (s13 = 0 ∧ (M.d 0 1 - M.d 1 3) < 2) ∨ (1 ≤ s13 ∧ (s13 : ℝ)+1 ≤ (M.d 0 1 - M.d 1 3) ∧ (M.d 0 1 - M.d 1 3) < (s13 : ℝ)+2) at hbridge13
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
  have hsort3 : ([M.d 3 4, M.d 1 3, M.d 0 3, M.d 2 3] : List ℝ).Pairwise (· ≤ ·) := by
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
  have hperm3 := hp3.trans (((((((List.Perm.swap (M.d 3 4) (M.d 2 3) []).cons (M.d 1 3)).cons (M.d 0 3)).trans ((List.Perm.swap (M.d 3 4) (M.d 1 3) [M.d 2 3]).cons (M.d 0 3))).trans (List.Perm.swap (M.d 3 4) (M.d 0 3) [M.d 1 3, M.d 2 3])).trans ((List.Perm.swap (M.d 1 3) (M.d 0 3) [M.d 2 3]).cons (M.d 3 4))))
  have hrow3 : M.rowxs 3 = [M.d 3 4, M.d 1 3, M.d 0 3, M.d 2 3] := hperm3.eq_of_pairwise' (M.row_sorted 3) hsort3
  have hrow_nonneg3 := SmallScoreGapBounds.model_gaps_nonneg M 3
  simp only [SmallScoreGapBounds.modelGaps, hrow3, StrongGapBudget.linearGaps] at hrow_nonneg3
  norm_num only [Nat.cast_ofNat] at hrow_nonneg3
  let s30 : ℕ := ⌊(M.d 3 4 - M.theta 3)⌋₊ - 1
  have hnonneg30 : 0 ≤ (M.d 3 4 - M.theta 3) := hrow_nonneg3 (M.d 3 4 - M.theta 3) (by simp)
  have hscore30a : (0 : ℝ) ≤ s30 := Nat.cast_nonneg s30
  have hbridge30 := score_gap_dichotomy (M.d 3 4 - M.theta 3) hnonneg30
  change (s30 = 0 ∧ (M.d 3 4 - M.theta 3) < 2) ∨ (1 ≤ s30 ∧ (s30 : ℝ)+1 ≤ (M.d 3 4 - M.theta 3) ∧ (M.d 3 4 - M.theta 3) < (s30 : ℝ)+2) at hbridge30
  let s31 : ℕ := ⌊(M.d 1 3 - M.d 3 4)⌋₊ - 1
  have hnonneg31 : 0 ≤ (M.d 1 3 - M.d 3 4) := hrow_nonneg3 (M.d 1 3 - M.d 3 4) (by simp)
  have hscore31a : (0 : ℝ) ≤ s31 := Nat.cast_nonneg s31
  have hbridge31 := score_gap_dichotomy (M.d 1 3 - M.d 3 4) hnonneg31
  change (s31 = 0 ∧ (M.d 1 3 - M.d 3 4) < 2) ∨ (1 ≤ s31 ∧ (s31 : ℝ)+1 ≤ (M.d 1 3 - M.d 3 4) ∧ (M.d 1 3 - M.d 3 4) < (s31 : ℝ)+2) at hbridge31
  let s32 : ℕ := ⌊(M.d 0 3 - M.d 1 3)⌋₊ - 1
  have hnonneg32 : 0 ≤ (M.d 0 3 - M.d 1 3) := hrow_nonneg3 (M.d 0 3 - M.d 1 3) (by simp)
  have hscore32a : (0 : ℝ) ≤ s32 := Nat.cast_nonneg s32
  have hbridge32 := score_gap_dichotomy (M.d 0 3 - M.d 1 3) hnonneg32
  change (s32 = 0 ∧ (M.d 0 3 - M.d 1 3) < 2) ∨ (1 ≤ s32 ∧ (s32 : ℝ)+1 ≤ (M.d 0 3 - M.d 1 3) ∧ (M.d 0 3 - M.d 1 3) < (s32 : ℝ)+2) at hbridge32
  let s33 : ℕ := ⌊(M.d 2 3 - M.d 0 3)⌋₊ - 1
  have hnonneg33 : 0 ≤ (M.d 2 3 - M.d 0 3) := hrow_nonneg3 (M.d 2 3 - M.d 0 3) (by simp)
  have hscore33a : (0 : ℝ) ≤ s33 := Nat.cast_nonneg s33
  have hbridge33 := score_gap_dichotomy (M.d 2 3 - M.d 0 3) hnonneg33
  change (s33 = 0 ∧ (M.d 2 3 - M.d 0 3) < 2) ∨ (1 ≤ s33 ∧ (s33 : ℝ)+1 ≤ (M.d 2 3 - M.d 0 3) ∧ (M.d 2 3 - M.d 0 3) < (s33 : ℝ)+2) at hbridge33
  let s34 : ℕ := ⌊(M.theta 3 + (5 + M.delta) - M.d 2 3)⌋₊ - 1
  have hnonneg34 : 0 ≤ (M.theta 3 + (5 + M.delta) - M.d 2 3) := hrow_nonneg3 (M.theta 3 + (5 + M.delta) - M.d 2 3) (by simp)
  have hscore34a : (0 : ℝ) ≤ s34 := Nat.cast_nonneg s34
  have hbridge34 := score_gap_dichotomy (M.theta 3 + (5 + M.delta) - M.d 2 3) hnonneg34
  change (s34 = 0 ∧ (M.theta 3 + (5 + M.delta) - M.d 2 3) < 2) ∨ (1 ≤ s34 ∧ (s34 : ℝ)+1 ≤ (M.theta 3 + (5 + M.delta) - M.d 2 3) ∧ (M.theta 3 + (5 + M.delta) - M.d 2 3) < (s34 : ℝ)+2) at hbridge34
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
  have hsort4 : ([M.d 3 4, M.d 1 4, M.d 0 4, M.d 2 4] : List ℝ).Pairwise (· ≤ ·) := by
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
  have hperm4 := hp4.trans (((((((List.Perm.swap (M.d 3 4) (M.d 2 4) []).cons (M.d 1 4)).cons (M.d 0 4)).trans ((List.Perm.swap (M.d 3 4) (M.d 1 4) [M.d 2 4]).cons (M.d 0 4))).trans (List.Perm.swap (M.d 3 4) (M.d 0 4) [M.d 1 4, M.d 2 4])).trans ((List.Perm.swap (M.d 1 4) (M.d 0 4) [M.d 2 4]).cons (M.d 3 4))))
  have hrow4 : M.rowxs 4 = [M.d 3 4, M.d 1 4, M.d 0 4, M.d 2 4] := hperm4.eq_of_pairwise' (M.row_sorted 4) hsort4
  have hrow_nonneg4 := SmallScoreGapBounds.model_gaps_nonneg M 4
  simp only [SmallScoreGapBounds.modelGaps, hrow4, StrongGapBudget.linearGaps] at hrow_nonneg4
  norm_num only [Nat.cast_ofNat] at hrow_nonneg4
  let s40 : ℕ := ⌊(M.d 3 4 - M.theta 4)⌋₊ - 1
  have hnonneg40 : 0 ≤ (M.d 3 4 - M.theta 4) := hrow_nonneg4 (M.d 3 4 - M.theta 4) (by simp)
  have hscore40a : (0 : ℝ) ≤ s40 := Nat.cast_nonneg s40
  have hbridge40 := score_gap_dichotomy (M.d 3 4 - M.theta 4) hnonneg40
  change (s40 = 0 ∧ (M.d 3 4 - M.theta 4) < 2) ∨ (1 ≤ s40 ∧ (s40 : ℝ)+1 ≤ (M.d 3 4 - M.theta 4) ∧ (M.d 3 4 - M.theta 4) < (s40 : ℝ)+2) at hbridge40
  let s41 : ℕ := ⌊(M.d 1 4 - M.d 3 4)⌋₊ - 1
  have hnonneg41 : 0 ≤ (M.d 1 4 - M.d 3 4) := hrow_nonneg4 (M.d 1 4 - M.d 3 4) (by simp)
  have hscore41a : (0 : ℝ) ≤ s41 := Nat.cast_nonneg s41
  have hbridge41 := score_gap_dichotomy (M.d 1 4 - M.d 3 4) hnonneg41
  change (s41 = 0 ∧ (M.d 1 4 - M.d 3 4) < 2) ∨ (1 ≤ s41 ∧ (s41 : ℝ)+1 ≤ (M.d 1 4 - M.d 3 4) ∧ (M.d 1 4 - M.d 3 4) < (s41 : ℝ)+2) at hbridge41
  let s42 : ℕ := ⌊(M.d 0 4 - M.d 1 4)⌋₊ - 1
  have hnonneg42 : 0 ≤ (M.d 0 4 - M.d 1 4) := hrow_nonneg4 (M.d 0 4 - M.d 1 4) (by simp)
  have hscore42a : (0 : ℝ) ≤ s42 := Nat.cast_nonneg s42
  have hbridge42 := score_gap_dichotomy (M.d 0 4 - M.d 1 4) hnonneg42
  change (s42 = 0 ∧ (M.d 0 4 - M.d 1 4) < 2) ∨ (1 ≤ s42 ∧ (s42 : ℝ)+1 ≤ (M.d 0 4 - M.d 1 4) ∧ (M.d 0 4 - M.d 1 4) < (s42 : ℝ)+2) at hbridge42
  let s43 : ℕ := ⌊(M.d 2 4 - M.d 0 4)⌋₊ - 1
  have hnonneg43 : 0 ≤ (M.d 2 4 - M.d 0 4) := hrow_nonneg4 (M.d 2 4 - M.d 0 4) (by simp)
  have hscore43a : (0 : ℝ) ≤ s43 := Nat.cast_nonneg s43
  have hbridge43 := score_gap_dichotomy (M.d 2 4 - M.d 0 4) hnonneg43
  change (s43 = 0 ∧ (M.d 2 4 - M.d 0 4) < 2) ∨ (1 ≤ s43 ∧ (s43 : ℝ)+1 ≤ (M.d 2 4 - M.d 0 4) ∧ (M.d 2 4 - M.d 0 4) < (s43 : ℝ)+2) at hbridge43
  let s44 : ℕ := ⌊(M.theta 4 + (5 + M.delta) - M.d 2 4)⌋₊ - 1
  have hnonneg44 : 0 ≤ (M.theta 4 + (5 + M.delta) - M.d 2 4) := hrow_nonneg4 (M.theta 4 + (5 + M.delta) - M.d 2 4) (by simp)
  have hscore44a : (0 : ℝ) ≤ s44 := Nat.cast_nonneg s44
  have hbridge44 := score_gap_dichotomy (M.theta 4 + (5 + M.delta) - M.d 2 4) hnonneg44
  change (s44 = 0 ∧ (M.theta 4 + (5 + M.delta) - M.d 2 4) < 2) ∨ (1 ≤ s44 ∧ (s44 : ℝ)+1 ≤ (M.theta 4 + (5 + M.delta) - M.d 2 4) ∧ (M.theta 4 + (5 + M.delta) - M.d 2 4) < (s44 : ℝ)+2) at hbridge44
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
              linarith only [hgap12a, hgap11a, hgap13a, hgap14a, hgap10a, hsum1]
            ·
              have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
              linarith only [hgap12a, hgap11a, htr013a, htr134a, hgap10a, ht23, ht12, hgap14b, hc34a, hgap13a, hdelta1, hsum1]
          ·
            have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
            rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
            ·
              have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
              linarith only [hgap14a, hdelta1, hc34a, ht12, hsum1, hgap12a, hgap10a, hgap13b, ht23, hgap11a, htr134a, hc01b]
            ·
              have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
              linarith only [hgap13b, ht23, hdelta1, hc34a, ht12, htr134a, hgap14a, hgap13a, hgap14b]
        ·
          have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
          rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
          ·
            have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
            rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
            ·
              have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
              linarith only [hc01b, htr134b, hgap11a, hc34a, hgap10a, ht23, hdelta1, hsum1, ht12, hgap12b, htr013a, hgap13a, hgap14a]
            ·
              have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
              linarith only [htr134b, htr013a, hc34a, ht23, hgap12a, hdelta1, hgap14b, hgap12b, hgap14a, ht12]
          ·
            have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
            linarith only [hgap13b, hdelta1, hc34a, hgap12b, hgap13a, hc01b, hgap12a, htr134b, ht23, ht12]
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
              linarith only [hc01b, hgap10a, hdelta1, hgap14a, hsum1, htr014a, hgap13a, hgap12a, hc12a, hgap11b]
            ·
              have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
              linarith only [hgap11b, hgap11a, htr134c, hgap14b, htr013a, hdelta1, hgap14a, hc12a]
          ·
            have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
            linarith only [htr134c, hgap13b, hc01b, hgap11b, hgap11a, hgap13a, hdelta1, hc12a]
        ·
          have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
          linarith only [hgap11a, hgap12b, hc01b, hdelta1, htr013a, hc12a, hgap12a, hgap11b]
    ·
      have hgap10a : (1 : ℝ) ≤ s10 := by exact_mod_cast hpositive10
      linarith only [hgap10b, hgap10a, htr012b, hgap00b, ht01]
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
            rcases hbridge30 with ⟨hzero30, hgap30b⟩ | ⟨hpositive30, hgap30b, hgap30c⟩
            ·
              have hgap30a : (s30 : ℝ) = 0 := by exact_mod_cast hzero30
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
                        linarith only [hgap44a, hgap40a, hsum4, hgap42a, hgap41a, hgap43a]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [htr024a, hgap42a, hsum0, hgap03a, hgap44b, hgap00b, hgap01a, hgap40a, hgap04a, hgap41a, ht0a, hgap43a, ht4b, hsum4, hgap02a, hdelta1]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [hgap00b, hgap01a, hgap04a, hdelta1, ht3b, hc23b, htr234c, htr024b, hgap43a, hgap43b, ht0a, hgap02a, hsum0, hgap03a]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    rcases hbridge31 with ⟨hzero31, hgap31b⟩ | ⟨hpositive31, hgap31b, hgap31c⟩
                    ·
                      have hgap31a : (s31 : ℝ) = 0 := by exact_mod_cast hzero31
                      rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                      ·
                        have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                        rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                        ·
                          have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                          linarith only [ht12, hdelta1, hsum4, htr013c, ht23, hgap43a, hgap40a, htr034c, hgap41a, hc34a, htr134b, hc01b, hgap42b, hgap44a]
                        ·
                          have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                          linarith only [hsum0, htr024a, ht4b, ht0a, hgap01a, hgap04a, hgap00b, hdelta1, hgap03a, hgap02a, hgap44a, hgap44b]
                      ·
                        have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                        linarith only [hdelta1, hgap01a, hgap03a, hc23b, htr024b, hsum0, ht0a, hgap43b, htr234c, hgap04a, hgap00b, hgap43a, hgap02a, ht3b]
                    ·
                      have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
                      rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                      ·
                        have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                        rcases hbridge10 with ⟨hzero10, hgap10b⟩ | ⟨hpositive10, hgap10b, hgap10c⟩
                        ·
                          have hgap10a : (s10 : ℝ) = 0 := by exact_mod_cast hzero10
                          rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                          ·
                            have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                            linarith only [hgap44a, hgap40a, htr034c, hc34a, hdelta1, htr134b, hc01b, hsum4, hgap43a, ht23, hgap41a, hgap42b, ht12, htr013c]
                          ·
                            have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                            linarith only [hdelta1, hgap04a, ht0a, hgap00b, hgap03a, hgap44a, ht4b, hsum0, hgap02a, hgap01a, htr024a, hgap44b]
                        ·
                          have hgap10a : (1 : ℝ) ≤ s10 := by exact_mod_cast hpositive10
                          rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                          ·
                            have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                            linarith only [htr134b, hdelta1, hc34a, htr034c, hgap41a, htr013c, hgap40a, hgap43a, hgap42b, ht23, hc01b, ht12, hgap44a, hsum4]
                          ·
                            have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                            linarith only [hgap42b, hgap04a, htr013c, hsum4, hgap02a, hgap40a, hdelta1, hgap01a, htr034c, ht0a, hgap10a, hsum0, hgap03a, ht4b, hgap10b, hc01b, htr124b, hgap44b, hgap43a, hgap00b, hgap41a, htr024a]
                      ·
                        have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                        linarith only [hgap01a, hdelta1, htr234c, hgap02a, ht3b, htr024b, hsum0, hgap04a, hgap43a, hc23b, hgap00b, hgap03a, hgap43b, ht0a]
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
                        linarith only [hgap41b, hdelta1, hgap43a, hc34a, hsum4, ht12, hgap42a, htr014a, hgap44a, hc01b, ht23, hgap40a]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [hgap04a, hc34a, hgap43a, hgap01a, hdelta1, ht4b, hgap40a, htr134c, hgap03a, hc01b, hsum4, htr013a, hgap00b, hgap44b, hgap41b, hgap02a, hsum0, ht12, hgap42a, htr024a, ht23, ht0a]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [ht3b, hdelta1, hgap01a, htr234c, htr024b, hgap43b, hgap00b, hc23b, hgap43a, ht0a, hgap04a, hsum0, hgap02a, hgap03a]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    linarith only [hdelta1, htr034c, hc34a, hgap41a, hgap42a, hgap42b, hgap41b, hc03b]
              ·
                have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
                linarith only [hgap40b, hgap30b, hgap40a, ht34]
            ·
              have hgap30a : (1 : ℝ) ≤ s30 := by exact_mod_cast hpositive30
              rcases hbridge31 with ⟨hzero31, hgap31b⟩ | ⟨hpositive31, hgap31b, hgap31c⟩
              ·
                have hgap31a : (s31 : ℝ) = 0 := by exact_mod_cast hzero31
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
                          linarith only [hgap41a, hgap44a, hsum4, hgap42a, hgap43a, hgap40a]
                        ·
                          have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                          linarith only [hsum0, hgap04a, hgap40a, hgap44b, hgap02a, ht4b, hgap42a, htr024a, ht0a, hsum4, hgap41a, hgap00b, hdelta1, hgap43a, hgap03a, hgap01a]
                      ·
                        have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                        linarith only [hgap02a, ht0a, hgap03a, hgap43b, hc23b, hsum0, hgap04a, htr024b, hdelta1, ht3b, htr234c, hgap01a, hgap00b, hgap43a]
                    ·
                      have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                      rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                      ·
                        have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                        rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                        ·
                          have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                          linarith only [hdelta1, hgap30b, hgap41a, hgap30a, hsum4, htr134b, htr034c, hgap43a, hgap42b, hgap40a, hgap44a, hc03b]
                        ·
                          have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                          linarith only [htr024a, htr013c, hgap44b, hsum0, hgap30b, ht12, hgap02a, hdelta1, htr034c, ht0a, hgap40a, hgap04a, hgap30a, hgap00b, hsum4, hgap01a, hgap42b, hgap41a, ht4b, hc01b, htr134b, hgap03a, ht23, hgap43a]
                      ·
                        have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                        linarith only [hgap30b, hgap42a, hgap43b, hdelta1, hgap43a, hgap42b, htr134b, hgap30a, hc23b, htr234c]
                  ·
                    have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                    linarith only [hgap30b, ht12, htr014a, hc01b, hgap41b, hdelta1, hgap41a, ht23, hgap30a]
                ·
                  have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
                  rcases hbridge32 with ⟨hzero32, hgap32b⟩ | ⟨hpositive32, hgap32b, hgap32c⟩
                  ·
                    have hgap32a : (s32 : ℝ) = 0 := by exact_mod_cast hzero32
                    rcases hbridge41 with ⟨hzero41, hgap41b⟩ | ⟨hpositive41, hgap41b, hgap41c⟩
                    ·
                      have hgap41a : (s41 : ℝ) = 0 := by exact_mod_cast hzero41
                      rcases hbridge42 with ⟨hzero42, hgap42b⟩ | ⟨hpositive42, hgap42b, hgap42c⟩
                      ·
                        have hgap42a : (s42 : ℝ) = 0 := by exact_mod_cast hzero42
                        rcases hbridge33 with ⟨hzero33, hgap33b⟩ | ⟨hpositive33, hgap33b, hgap33c⟩
                        ·
                          have hgap33a : (s33 : ℝ) = 0 := by exact_mod_cast hzero33
                          rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                          ·
                            have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                            rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                            ·
                              have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                              linarith only [hgap40b, hdelta1, ht3a, ht2b, hc01b, htr013a, hsum4, ht34, hgap42a, hgap44a, hgap41a, hgap43a, ht12, htr134a]
                            ·
                              have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                              linarith only [hgap41a, htr024a, ht1b, hgap02a, hsum0, hsum4, htr013a, htr134a, hgap03a, hgap01a, hgap40b, hgap42a, hgap44b, hdelta1, ht0a, hc01b, hgap43a, hgap00b, hgap04a]
                          ·
                            have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                            linarith only [hc23b, hdelta1, hgap04a, ht0a, htr024b, hsum0, hgap43a, hgap03a, hgap43b, htr234c, hgap00b, hgap01a, hgap02a, ht3b]
                        ·
                          have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                          linarith only [hgap01a, hgap33b, hgap03a, ht3b, hgap33a, hc23b, hdelta1, htr034c, hgap04a, htr024b, ht0a, hgap00b, hgap02a, hsum0]
                      ·
                        have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                        rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                        ·
                          have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                          rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                          ·
                            have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                            linarith only [htr034c, hdelta1, hgap40b, htr134b, ht34, hgap44a, hsum4, hgap42b, hgap41a, hgap43a, hc03b]
                          ·
                            have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                            linarith only [ht0a, ht4b, hgap01a, hgap44b, hdelta1, hgap00b, hgap44a, htr024a, hgap02a, hgap03a, hgap04a, hsum0]
                        ·
                          have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                          linarith only [hdelta1, hgap42b, htr134b, htr234c, hc23b, hgap40a, hgap43a, hgap42a, hgap40b, hgap43b, ht34]
                    ·
                      have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                      linarith only [hc01b, hgap40a, hgap40b, hgap41a, ht23, htr014a, hgap41b, ht34, hdelta1, ht12]
                  ·
                    have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                    linarith only [hgap40b, hgap32b, hgap32a, ht34, htr134a, hgap40a, hc03b, hdelta1]
              ·
                have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
                linarith only [hgap31a, hgap31b, ht23, hgap30a, hc01b, htr013a, hgap30b, hdelta1, ht12]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            rcases hbridge30 with ⟨hzero30, hgap30b⟩ | ⟨hpositive30, hgap30b, hgap30c⟩
            ·
              have hgap30a : (s30 : ℝ) = 0 := by exact_mod_cast hzero30
              rcases hbridge31 with ⟨hzero31, hgap31b⟩ | ⟨hpositive31, hgap31b, hgap31c⟩
              ·
                have hgap31a : (s31 : ℝ) = 0 := by exact_mod_cast hzero31
                rcases hbridge10 with ⟨hzero10, hgap10b⟩ | ⟨hpositive10, hgap10b, hgap10c⟩
                ·
                  have hgap10a : (s10 : ℝ) = 0 := by exact_mod_cast hzero10
                  rcases hbridge32 with ⟨hzero32, hgap32b⟩ | ⟨hpositive32, hgap32b, hgap32c⟩
                  ·
                    have hgap32a : (s32 : ℝ) = 0 := by exact_mod_cast hzero32
                    rcases hbridge33 with ⟨hzero33, hgap33b⟩ | ⟨hpositive33, hgap33b, hgap33c⟩
                    ·
                      have hgap33a : (s33 : ℝ) = 0 := by exact_mod_cast hzero33
                      rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                      ·
                        have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
                        linarith only [hsum3, hgap34a, hgap33a, hgap30a, hgap32a, hgap31a]
                      ·
                        have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                        linarith only [htr024a, hdelta1, hgap31a, htr134a, hgap34b, hgap02a, hgap03a, hgap04b, hsum3, hc34a, hgap32a, hsum0, hgap00b, hgap33a, htr013a, hgap30a, htr234c, hgap01a]
                    ·
                      have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                      rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                      ·
                        have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
                        linarith only [hgap31a, hsum0, hgap33b, hsum3, htr034c, hgap32a, htr134a, hgap01a, hdelta1, hgap30a, htr013a, hgap00b, hgap02a, hgap03a, hgap34a, hgap04b, hc34a, htr024b, hc23b]
                      ·
                        have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                        linarith only [htr024b, htr034c, hgap33a, hgap34a, hgap02a, hgap33b, hdelta1, htr134a, hgap34b, hgap03a, hsum0, hgap01a, hgap00b, hc34a, htr013a, hgap04b]
                  ·
                    have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                    linarith only [hdelta1, ht01, htr013c, hgap32b, hgap04b, ht12, hgap04a, ht23, hgap32a, hc34a, htr134a]
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
                            linarith only [hgap42a, hgap40a, hgap41a, hgap44a, hsum4, hgap43a]
                          ·
                            have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                            linarith only [hdelta1, ht23, hsum0, hgap00b, hc34a, hgap40a, ht4b, hgap41a, hgap44b, hgap43a, htr134a, htr024a, hsum4, hgap03a, ht1a, htr013a, hgap01a, ht12, hgap04b, hgap02a, hgap42a]
                        ·
                          have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                          rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                          ·
                            have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                            linarith only [hc23b, htr024b, hgap00b, hsum0, htr013a, hdelta1, hgap40a, hc34a, hgap03a, hgap43b, hgap42a, htr234c, hgap41a, hgap02a, hsum4, hgap01a, htr134a, hgap04b, hgap44a]
                          ·
                            have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                            linarith only [hgap04b, hgap41a, ht4b, hc34a, hgap03a, hgap01a, ht1a, hsum4, hsum0, hdelta1, htr024b, hgap00b, hgap44b, ht12, hgap42a, htr013a, hgap43b, hgap40a, htr134a, ht23, hgap02a]
                      ·
                        have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                        linarith only [hgap42b, hdelta1, hgap10a, hgap10b, hgap04a, hgap04b, htr034c, htr013c, htr124b, ht01, hgap42a]
                    ·
                      have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                      linarith only [hgap41b, hgap31b, htr134c, hgap41a]
                  ·
                    have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
                    linarith only [hgap40a, hgap40b, ht34, hgap30b]
              ·
                have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
                linarith only [htr013a, hc34a, hgap31b, ht12, ht01, hdelta1, hgap31a, hgap04a, ht23, hgap04b]
            ·
              have hgap30a : (1 : ℝ) ≤ s30 := by exact_mod_cast hpositive30
              linarith only [hgap30a, ht23, ht01, hgap04a, hdelta1, hgap30b, htr013a, hgap04b, ht12, htr134a]
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
                    linarith only [hgap40a, hsum4, hgap43a, hgap42a, hgap44a, hgap41a]
                  ·
                    have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                    linarith only [hgap43a, ht4b, hgap41a, hdelta1, htr024a, hgap00a, hgap40a, ht0a, hsum4, hgap42a, hgap00b, hgap44b]
                ·
                  have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                  rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                  ·
                    have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                    linarith only [hgap44a, hdelta1, hgap40a, hsum4, hgap43b, ht0a, htr234c, htr024b, ht3b, hgap00a, hc23b, hgap00b, hgap42a, hgap41a]
                  ·
                    have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                    linarith only [hgap42a, hgap00b, hsum4, ht0a, htr024b, hgap00a, hgap43b, hgap41a, hgap44b, hdelta1, ht4b, hgap40a]
              ·
                have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                linarith only [hc34a, htr034c, hgap03a, hc01b, hdelta1, ht23, hgap42b, ht12, htr134b, hgap03b, hgap42a]
            ·
              have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
              linarith only [htr014b, hgap03a, hdelta1, hgap41a, htr034c, hgap03b, hc34a, ht23, hc01b, ht12, hgap41b]
          ·
            have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
            linarith only [hdelta1, hgap03a, hc01b, hgap03b, ht12, hgap40a, htr134a, hgap40b, ht34, ht23, htr013b]
      ·
        have hgap02a : (1 : ℝ) ≤ s02 := by exact_mod_cast hpositive02
        rcases hbridge10 with ⟨hzero10, hgap10b⟩ | ⟨hpositive10, hgap10b, hgap10c⟩
        ·
          have hgap10a : (s10 : ℝ) = 0 := by exact_mod_cast hzero10
          rcases hbridge11 with ⟨hzero11, hgap11b⟩ | ⟨hpositive11, hgap11b, hgap11c⟩
          ·
            have hgap11a : (s11 : ℝ) = 0 := by exact_mod_cast hzero11
            rcases hbridge12 with ⟨hzero12, hgap12b⟩ | ⟨hpositive12, hgap12b, hgap12c⟩
            ·
              have hgap12a : (s12 : ℝ) = 0 := by exact_mod_cast hzero12
              rcases hbridge30 with ⟨hzero30, hgap30b⟩ | ⟨hpositive30, hgap30b, hgap30c⟩
              ·
                have hgap30a : (s30 : ℝ) = 0 := by exact_mod_cast hzero30
                rcases hbridge40 with ⟨hzero40, hgap40b⟩ | ⟨hpositive40, hgap40b, hgap40c⟩
                ·
                  have hgap40a : (s40 : ℝ) = 0 := by exact_mod_cast hzero40
                  rcases hbridge41 with ⟨hzero41, hgap41b⟩ | ⟨hpositive41, hgap41b, hgap41c⟩
                  ·
                    have hgap41a : (s41 : ℝ) = 0 := by exact_mod_cast hzero41
                    rcases hbridge42 with ⟨hzero42, hgap42b⟩ | ⟨hpositive42, hgap42b, hgap42c⟩
                    ·
                      have hgap42a : (s42 : ℝ) = 0 := by exact_mod_cast hzero42
                      rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
                      ·
                        have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
                        rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
                        ·
                          have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                          linarith only [hgap13a, hgap11a, hgap12a, hgap14a, hsum1, hgap10a]
                        ·
                          have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                          linarith only [hgap13a, hgap00a, ht1b, hgap02b, hdelta1, hgap00b, hgap10a, ht0a, hgap11a, htr013c, htr024b, hgap14b, hsum1, hgap02a, hgap12a]
                      ·
                        have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
                        rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
                        ·
                          have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                          linarith only [hgap14a, ht23, hsum1, htr134a, hc34a, hdelta1, hgap13b, ht12, hc01b, hgap12a, hgap10a, hgap11a]
                        ·
                          have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                          linarith only [hc34a, htr134a, hgap14a, ht23, hgap14b, hdelta1, hgap13b, hgap13a, ht12]
                    ·
                      have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                      linarith only [htr013c, hc01b, hgap42a, hgap02b, hdelta1, ht23, hgap02a, hgap42b, hc34a, ht12, htr134b]
                  ·
                    have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                    linarith only [hc34a, hgap02b, htr014b, hc03b, hdelta1, hgap41a, hgap02a, hgap41b]
                ·
                  have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
                  linarith only [hgap30b, ht34, hgap40a, hgap40b]
              ·
                have hgap30a : (1 : ℝ) ≤ s30 := by exact_mod_cast hpositive30
                rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
                ·
                  have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
                  rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
                  ·
                    have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                    linarith only [hgap14a, hsum1, hgap12a, hgap10a, hgap11a, hgap13a]
                  ·
                    have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                    linarith only [ht12, hgap10a, htr134b, hgap30b, hdelta1, hgap13a, hgap12a, htr013c, hsum1, hgap14b, hgap02a, hgap30a, htr014b, ht23, hgap11a, hgap02b]
                ·
                  have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
                  linarith only [hgap13b, hgap13a, hc01b, htr134a, ht23, hgap30a, hdelta1, ht12, hgap30b]
            ·
              have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
              rcases hbridge40 with ⟨hzero40, hgap40b⟩ | ⟨hpositive40, hgap40b, hgap40c⟩
              ·
                have hgap40a : (s40 : ℝ) = 0 := by exact_mod_cast hzero40
                rcases hbridge13 with ⟨hzero13, hgap13b⟩ | ⟨hpositive13, hgap13b, hgap13c⟩
                ·
                  have hgap13a : (s13 : ℝ) = 0 := by exact_mod_cast hzero13
                  rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
                  ·
                    have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
                    linarith only [hgap11a, htr134b, hsum1, ht12, hgap13a, hc34a, htr013a, ht23, hdelta1, hgap12b, hc01b, hgap14a, hgap10a]
                  ·
                    have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                    linarith only [hgap12a, hc34a, htr134b, hgap14a, ht23, hgap12b, ht12, htr013a, hgap14b, hdelta1]
                ·
                  have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
                  linarith only [hgap12a, hc01b, htr134b, hgap13a, ht12, hgap12b, ht23, hgap13b, hdelta1, hc34a]
              ·
                have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
                linarith only [hgap12a, htr134b, hdelta1, ht34, hgap12b, hgap40b, htr013a, ht23, ht12, hc01b, hgap40a]
          ·
            have hgap11a : (1 : ℝ) ≤ s11 := by exact_mod_cast hpositive11
            linarith only [htr014b, hgap11b, hgap02b, hgap02a, hgap11a, htr013c, hc12a, hdelta1, hc01b]
        ·
          have hgap10a : (1 : ℝ) ≤ s10 := by exact_mod_cast hpositive10
          rcases hbridge30 with ⟨hzero30, hgap30b⟩ | ⟨hpositive30, hgap30b, hgap30c⟩
          ·
            have hgap30a : (s30 : ℝ) = 0 := by exact_mod_cast hzero30
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
                      linarith only [hsum4, hgap44a, hgap41a, hgap43a, hgap40a, hgap42a]
                    ·
                      have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                      linarith only [ht01, hgap42a, htr012b, hgap10a, hgap44b, hgap40a, ht4b, hgap41a, hgap10b, hdelta1, hsum4, htr024a, hgap43a, ht0a]
                  ·
                    have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                    rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                    ·
                      have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                      linarith only [ht4b, hsum4, hgap41a, hgap43b, hgap42a, hdelta1, ht0a, hgap44a, hgap10b, hgap40a, ht01, hc24b, htr012b, htr024b, hgap10a]
                    ·
                      have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                      linarith only [hgap10b, ht01, hgap42a, hgap43b, hgap40a, hgap10a, hsum4, htr012b, ht4b, hgap41a, htr024b, hdelta1, ht0a, hgap44b]
                ·
                  have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                  linarith only [htr013c, hdelta1, hgap02b, htr124b, hgap02a, hgap42b, hgap10a, hgap10b, hgap42a, hc01b]
              ·
                have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                linarith only [hgap02b, hgap02a, htr013c, hc01b, htr014b, ht12, hgap41a, hdelta1, hgap41b, ht23, hc34a]
            ·
              have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
              linarith only [ht34, hgap40b, hgap40a, hgap30b]
          ·
            have hgap30a : (1 : ℝ) ≤ s30 := by exact_mod_cast hpositive30
            rcases hbridge31 with ⟨hzero31, hgap31b⟩ | ⟨hpositive31, hgap31b, hgap31c⟩
            ·
              have hgap31a : (s31 : ℝ) = 0 := by exact_mod_cast hzero31
              rcases hbridge32 with ⟨hzero32, hgap32b⟩ | ⟨hpositive32, hgap32b, hgap32c⟩
              ·
                have hgap32a : (s32 : ℝ) = 0 := by exact_mod_cast hzero32
                rcases hbridge33 with ⟨hzero33, hgap33b⟩ | ⟨hpositive33, hgap33b, hgap33c⟩
                ·
                  have hgap33a : (s33 : ℝ) = 0 := by exact_mod_cast hzero33
                  rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                  ·
                    have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
                    linarith only [hsum3, hgap02a, htr034b, hdelta1, hgap02b, hgap34a, ht23, hc01b, hgap31a, hgap30b, hgap33a, htr013c, hgap32a, ht12]
                  ·
                    have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                    linarith only [hgap34b, hgap02b, hgap30a, htr134b, hgap34a, hdelta1, htr014b, hgap30b, hgap02a, htr023c]
                ·
                  have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                  linarith only [htr014b, hgap02b, hgap30b, hc23b, hgap30a, hdelta1, hgap33b, hgap33a, hgap02a, htr134b]
              ·
                have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                linarith only [hgap32a, hgap32b, hdelta1, ht23, htr013c, hgap30a, ht12, htr134a, hc01b, hgap30b]
            ·
              have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
              linarith only [ht12, hgap30b, hgap31a, htr013a, hc01b, hdelta1, hgap31b, hgap30a, ht23]
    ·
      have hgap01a : (1 : ℝ) ≤ s01 := by exact_mod_cast hpositive01
      rcases hbridge02 with ⟨hzero02, hgap02b⟩ | ⟨hpositive02, hgap02b, hgap02c⟩
      ·
        have hgap02a : (s02 : ℝ) = 0 := by exact_mod_cast hzero02
        rcases hbridge10 with ⟨hzero10, hgap10b⟩ | ⟨hpositive10, hgap10b, hgap10c⟩
        ·
          have hgap10a : (s10 : ℝ) = 0 := by exact_mod_cast hzero10
          rcases hbridge03 with ⟨hzero03, hgap03b⟩ | ⟨hpositive03, hgap03b, hgap03c⟩
          ·
            have hgap03a : (s03 : ℝ) = 0 := by exact_mod_cast hzero03
            rcases hbridge04 with ⟨hzero04, hgap04b⟩ | ⟨hpositive04, hgap04b, hgap04c⟩
            ·
              have hgap04a : (s04 : ℝ) = 0 := by exact_mod_cast hzero04
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
                        linarith only [hgap44a, hgap42a, hgap43a, hsum4, hgap40a, hgap41a]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [hdelta1, hgap03a, htr024c, hgap43a, hgap44b, hgap02a, hgap01b, hgap40a, ht4b, hsum0, hgap42a, hgap04a, hsum4, hgap00b, hgap41a, ht0a]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [hgap03a, hc24b, hgap43a, hgap43b, hgap02a, hsum0, ht4b, hgap00b, hdelta1, ht0a, hgap04a, hgap01b]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                    ·
                      have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                      rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                      ·
                        have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                        linarith only [hc34a, hdelta1, hgap44a, htr013c, hgap40a, hsum4, hgap42b, hgap41a, hgap43a, htr134b, htr034c, hc01b, ht23, ht12]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [hgap00b, ht0a, htr024c, hgap03a, hgap44b, hsum0, hgap02a, hgap04a, ht4b, hgap44a, hdelta1, hgap01b]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [hgap43b, hgap04a, hgap02a, hgap43a, hgap03a, ht4b, hdelta1, hgap00b, ht0a, hgap01b, hc24b, hsum0]
                ·
                  have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                  rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                  ·
                    have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
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
                            linarith only [hdelta1, hgap41b, hc13b, hgap43a, htr134c, hsum4, hc34a, hgap42a, hgap40a, hgap44a]
                          ·
                            have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                            linarith only [hdelta1, hgap41b, ht4b, htr013a, hgap42a, hgap00b, hgap02a, htr134c, htr024c, hsum0, hgap40a, hc01b, hgap44b, hgap43a, hsum4, hgap04a, ht23, hgap01b, hgap03a, ht0a, hc34a, ht12]
                        ·
                          have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                          linarith only [hgap00b, ht1b, hdelta1, hgap03a, hgap04a, htr034c, hgap02a, htr013c, hsum0, hgap14b, ht0a, hgap01b, hgap14a]
                      ·
                        have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                        linarith only [hgap01b, hc24b, hgap02a, hsum0, hgap43b, hdelta1, ht4b, hgap43a, hgap03a, hgap04a, ht0a, hgap00b]
                    ·
                      have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                      linarith only [hgap42b, hgap42a, hgap41a, hc01b, hgap41b, ht23, hdelta1, hc34a, ht12, htr013c, htr034c]
                  ·
                    have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                    linarith only [ht0a, htr034c, hgap01b, hgap00b, hgap02a, ht3b, hgap34a, hgap04a, hdelta1, hgap34b, htr023c, hgap03a, hsum0]
              ·
                have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
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
                        linarith only [hdelta1, hgap43a, hsum4, htr013c, hgap40b, ht23, ht12, hgap42a, hgap44a, hgap41a, ht34, hc01b, htr034a]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [hgap03a, ht0a, hgap42a, hgap43a, hdelta1, htr134a, hgap02a, htr024c, hgap41a, hc01b, hsum4, hgap04a, ht1b, htr013a, hgap01b, hgap44b, hgap40b, hgap00b, hsum0]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [hgap03a, ht0a, hc24b, hgap43a, hdelta1, hgap43b, ht4b, hgap02a, hsum0, hgap04a, hgap00b, hgap01b]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    rcases hbridge11 with ⟨hzero11, hgap11b⟩ | ⟨hpositive11, hgap11b, hgap11c⟩
                    ·
                      have hgap11a : (s11 : ℝ) = 0 := by exact_mod_cast hzero11
                      rcases hbridge30 with ⟨hzero30, hgap30b⟩ | ⟨hpositive30, hgap30b, hgap30c⟩
                      ·
                        have hgap30a : (s30 : ℝ) = 0 := by exact_mod_cast hzero30
                        linarith only [hgap40b, ht34, hgap30b, hgap40a]
                      ·
                        have hgap30a : (1 : ℝ) ≤ s30 := by exact_mod_cast hpositive30
                        rcases hbridge12 with ⟨hzero12, hgap12b⟩ | ⟨hpositive12, hgap12b, hgap12c⟩
                        ·
                          have hgap12a : (s12 : ℝ) = 0 := by exact_mod_cast hzero12
                          rcases hbridge31 with ⟨hzero31, hgap31b⟩ | ⟨hpositive31, hgap31b, hgap31c⟩
                          ·
                            have hgap31a : (s31 : ℝ) = 0 := by exact_mod_cast hzero31
                            rcases hbridge32 with ⟨hzero32, hgap32b⟩ | ⟨hpositive32, hgap32b, hgap32c⟩
                            ·
                              have hgap32a : (s32 : ℝ) = 0 := by exact_mod_cast hzero32
                              rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                              ·
                                have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                                rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                                ·
                                  have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                                  linarith only [hdelta1, ht34, hc01b, htr034c, hgap42b, hgap44a, hgap41a, ht23, htr013c, hsum4, ht12, htr134b, hgap43a, hgap40b]
                                ·
                                  have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                                  linarith only [hsum0, ht0a, hgap44a, hgap00b, hgap03a, hgap01b, htr024c, hdelta1, ht4b, hgap44b, hgap02a, hgap04a]
                              ·
                                have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                                linarith only [hgap43a, hgap43b, hsum0, hgap04a, hgap02a, hgap01b, ht0a, ht4b, hgap03a, hgap00b, hdelta1, hc24b]
                            ·
                              have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                              linarith only [ht23, htr134a, hdelta1, ht12, hc01b, hgap40a, hgap32b, hgap32a, ht34, hgap40b, htr013c]
                          ·
                            have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
                            linarith only [hc01b, hdelta1, hgap40a, hgap31b, hgap40b, ht34, htr013a, ht12, ht23, hgap31a]
                        ·
                          have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
                          linarith only [hdelta1, hgap12b, htr013a, hc01b, ht23, hgap40b, htr134b, hgap12a, ht12, ht34, hgap40a]
                    ·
                      have hgap11a : (1 : ℝ) ≤ s11 := by exact_mod_cast hpositive11
                      linarith only [hc01b, hc12a, hgap42a, hgap11a, hgap11b, hgap42b, hdelta1, htr013c, htr034c]
                ·
                  have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                  linarith only [hc01b, hgap40b, hgap41a, htr014a, hgap41b, hgap40a, hdelta1, ht34, ht23, ht12]
            ·
              have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
              linarith only [hdelta1, hgap04a, htr034c, hgap00b, hgap00a, hgap04b, hgap01a, hgap01b, htr013c]
          ·
            have hgap03a : (1 : ℝ) ≤ s03 := by exact_mod_cast hpositive03
            linarith only [hgap01a, hgap03b, hgap00b, ht12, hgap01b, hc01b, ht0a, hdelta1, ht34, hgap03a, hgap00a, ht23, htr034c, ht4b]
        ·
          have hgap10a : (1 : ℝ) ≤ s10 := by exact_mod_cast hpositive10
          rcases hbridge03 with ⟨hzero03, hgap03b⟩ | ⟨hpositive03, hgap03b, hgap03c⟩
          ·
            have hgap03a : (s03 : ℝ) = 0 := by exact_mod_cast hzero03
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
                    linarith only [hgap12a, hdelta1, hsum1, htr034c, hgap01b, hc01b, htr012b, hgap11a, hgap10b, hgap14a, htr013c, hgap13a, hgap01a]
                  ·
                    have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                    linarith only [hgap10b, hgap10a, htr012b, hgap01a, hgap14a, hgap14b, hgap01b, htr013c, htr034c, hdelta1]
                ·
                  have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
                  rcases hbridge04 with ⟨hzero04, hgap04b⟩ | ⟨hpositive04, hgap04b, hgap04c⟩
                  ·
                    have hgap04a : (s04 : ℝ) = 0 := by exact_mod_cast hzero04
                    rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                    ·
                      have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
                      rcases hbridge40 with ⟨hzero40, hgap40b⟩ | ⟨hpositive40, hgap40b, hgap40c⟩
                      ·
                        have hgap40a : (s40 : ℝ) = 0 := by exact_mod_cast hzero40
                        rcases hbridge30 with ⟨hzero30, hgap30b⟩ | ⟨hpositive30, hgap30b, hgap30c⟩
                        ·
                          have hgap30a : (s30 : ℝ) = 0 := by exact_mod_cast hzero30
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
                                  linarith only [hsum4, hgap43a, hgap42a, hgap44a, hgap40a, hgap41a]
                                ·
                                  have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                                  linarith only [hsum4, ht4b, hsum0, htr024c, hgap42a, hgap43a, hgap44b, hgap03a, hdelta1, hgap02a, hgap41a, hgap00b, hgap01b, hgap40a, ht0a, hgap04a]
                              ·
                                have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                                linarith only [hdelta1, hgap43a, hgap03a, ht4b, hgap02a, ht0a, hgap00b, hgap01b, hc24b, hgap43b, hsum0, hgap04a]
                            ·
                              have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                              rcases hbridge31 with ⟨hzero31, hgap31b⟩ | ⟨hpositive31, hgap31b, hgap31c⟩
                              ·
                                have hgap31a : (s31 : ℝ) = 0 := by exact_mod_cast hzero31
                                rcases hbridge32 with ⟨hzero32, hgap32b⟩ | ⟨hpositive32, hgap32b, hgap32c⟩
                                ·
                                  have hgap32a : (s32 : ℝ) = 0 := by exact_mod_cast hzero32
                                  rcases hbridge33 with ⟨hzero33, hgap33b⟩ | ⟨hpositive33, hgap33b, hgap33c⟩
                                  ·
                                    have hgap33a : (s33 : ℝ) = 0 := by exact_mod_cast hzero33
                                    linarith only [hgap31a, hgap34a, hgap30a, hgap33a, hgap32a, hsum3]
                                  ·
                                    have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                                    linarith only [hgap01b, hsum0, ht3b, hgap04a, hgap30a, hgap32a, htr034c, hgap02a, hgap00b, hdelta1, hsum3, hgap03a, hgap34a, hgap33b, ht0a, hgap31a, hc23b]
                                ·
                                  have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                                  rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                                  ·
                                    have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                                    rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                                    ·
                                      have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                                      linarith only [hgap40a, hdelta1, hsum4, hc01b, htr124b, hgap43a, hgap44a, hgap10b, htr013c, hgap41a, hgap10a, hgap42b, htr034c]
                                    ·
                                      have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                                      linarith only [ht4b, hgap10b, hgap01b, htr034c, hgap03a, hgap40a, htr124b, htr013c, hgap04a, hgap10a, hgap41a, hsum0, hdelta1, hc01b, hgap42b, hgap44b, hgap43a, ht0a, hgap02a, hsum4, hgap00b, htr024c]
                                  ·
                                    have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                                    linarith only [hgap43b, hc24b, hgap02a, hdelta1, hgap01b, hgap03a, hsum0, hgap00b, ht0a, hgap04a, hgap43a, ht4b]
                              ·
                                have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
                                linarith only [hgap13a, ht12, ht23, hc01b, hdelta1, hc34a, hgap31b, hgap31a, hgap13b]
                          ·
                            have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                            linarith only [hc34a, ht12, hgap41a, hdelta1, hc01b, htr134c, hgap41b, hgap13b, hgap13a, ht23]
                        ·
                          have hgap30a : (1 : ℝ) ≤ s30 := by exact_mod_cast hpositive30
                          linarith only [hc01b, htr134a, ht23, hgap13a, hgap30a, hgap30b, hdelta1, hgap13b, ht12]
                      ·
                        have hgap40a : (1 : ℝ) ≤ s40 := by exact_mod_cast hpositive40
                        linarith only [ht12, ht34, hdelta1, hgap40b, hgap40a, htr134a, ht23, hc01b, hgap13a, hgap13b]
                    ·
                      have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                      linarith only [ht3b, hgap02a, htr023c, hgap00b, ht0a, hdelta1, hgap01b, hgap34b, hgap04a, hgap03a, hgap34a, hsum0, htr034c]
                  ·
                    have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
                    linarith only [hgap10a, hgap01a, hgap04b, htr012b, hgap04a, ht01, hdelta1, htr013c, htr034c, hgap01b, hgap10b]
              ·
                have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
                linarith only [hdelta1, htr013a, hgap12a, hc01b, hgap12b, htr124b, hgap10b, hgap10a]
            ·
              have hgap11a : (1 : ℝ) ≤ s11 := by exact_mod_cast hpositive11
              linarith only [hdelta1, hc01b, hgap10b, htr014a, hgap10a, hgap11b, hgap11a]
          ·
            have hgap03a : (1 : ℝ) ≤ s03 := by exact_mod_cast hpositive03
            linarith only [htr012b, hgap01b, hgap01a, hgap10a, htr034c, hdelta1, hgap03b, hgap03a, hgap10b, hc01b]
      ·
        have hgap02a : (1 : ℝ) ≤ s02 := by exact_mod_cast hpositive02
        linarith only [htr013c, hgap02a, hgap02b, hgap01a, ht12, hdelta1, hc01b, ht23, hgap01b, hgap00b, ht34, ht0a, hgap00a, ht4b]

#print axioms n5_between_mask807
end Jsp404.SixExactFloorKernel
