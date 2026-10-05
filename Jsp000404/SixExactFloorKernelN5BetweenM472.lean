import Jsp000404.SixExactFloorKernelPrimitives

/-! Representative exact-score certificate. A fixed orientation is an explicit
hypothesis only for this probe; public wrappers must split every triangle arm. -/
namespace Jsp404.SixExactFloorKernel

set_option maxHeartbeats 16000000 in
theorem n5_between_mask472 (M : SixModelCompression.ModelSix 5)
    (hhigh : (1/2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    (htri012 : M.d 0 1+1 ≤ M.d 1 2 ∧ M.d 0 1 < M.d 0 2 ∧ M.d 0 2 < M.d 1 2)
    (htri013 : M.d 0 1+1 ≤ M.d 1 3 ∧ M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (htri014 : M.d 0 1+1 ≤ M.d 1 4 ∧ M.d 0 1 < M.d 0 4 ∧ M.d 0 4 < M.d 1 4)
    (htri023 : M.d 2 3+1 ≤ M.d 0 2 ∧ M.d 2 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 2)
    (htri024 : M.d 2 4+1 ≤ M.d 0 2 ∧ M.d 2 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 2)
    (htri034 : M.d 0 3+1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (htri123 : M.d 2 3+1 ≤ M.d 1 2 ∧ M.d 2 3 < M.d 1 3 ∧ M.d 1 3 < M.d 1 2)
    (htri124 : M.d 2 4+1 ≤ M.d 1 2 ∧ M.d 2 4 < M.d 1 4 ∧ M.d 1 4 < M.d 1 2)
    (htri134 : M.d 3 4+1 ≤ M.d 1 3 ∧ M.d 3 4 < M.d 1 4 ∧ M.d 1 4 < M.d 1 3)
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
  have hsort0 : ([M.d 0 1, M.d 0 3, M.d 0 4, M.d 0 2] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp0 := M.row_perm 0
  have he0 : (((List.finRange 5).erase (0 : Fin 5)).map (M.d 0)) = [M.d 0 1, M.d 0 2, M.d 0 3, M.d 0 4] := by
    norm_num [List.finRange, List.ofFn_succ]
  rw [he0] at hp0
  have hperm0 := hp0.trans ((((List.Perm.swap (M.d 0 3) (M.d 0 2) [M.d 0 4]).cons (M.d 0 1)).trans (((List.Perm.swap (M.d 0 4) (M.d 0 2) []).cons (M.d 0 3)).cons (M.d 0 1))))
  have hrow0 : M.rowxs 0 = [M.d 0 1, M.d 0 3, M.d 0 4, M.d 0 2] := hperm0.eq_of_pairwise' (M.row_sorted 0) hsort0
  have hrow_nonneg0 := SmallScoreGapBounds.model_gaps_nonneg M 0
  simp only [SmallScoreGapBounds.modelGaps, hrow0, StrongGapBudget.linearGaps] at hrow_nonneg0
  norm_num only [Nat.cast_ofNat] at hrow_nonneg0
  let s00 : ℕ := ⌊(M.d 0 1 - M.theta 0)⌋₊ - 1
  have hnonneg00 : 0 ≤ (M.d 0 1 - M.theta 0) := hrow_nonneg0 (M.d 0 1 - M.theta 0) (by simp)
  have hscore00a : (0 : ℝ) ≤ s00 := Nat.cast_nonneg s00
  have hbridge00 := score_gap_dichotomy (M.d 0 1 - M.theta 0) hnonneg00
  change (s00 = 0 ∧ (M.d 0 1 - M.theta 0) < 2) ∨ (1 ≤ s00 ∧ (s00 : ℝ)+1 ≤ (M.d 0 1 - M.theta 0) ∧ (M.d 0 1 - M.theta 0) < (s00 : ℝ)+2) at hbridge00
  let s01 : ℕ := ⌊(M.d 0 3 - M.d 0 1)⌋₊ - 1
  have hnonneg01 : 0 ≤ (M.d 0 3 - M.d 0 1) := hrow_nonneg0 (M.d 0 3 - M.d 0 1) (by simp)
  have hscore01a : (0 : ℝ) ≤ s01 := Nat.cast_nonneg s01
  have hbridge01 := score_gap_dichotomy (M.d 0 3 - M.d 0 1) hnonneg01
  change (s01 = 0 ∧ (M.d 0 3 - M.d 0 1) < 2) ∨ (1 ≤ s01 ∧ (s01 : ℝ)+1 ≤ (M.d 0 3 - M.d 0 1) ∧ (M.d 0 3 - M.d 0 1) < (s01 : ℝ)+2) at hbridge01
  let s02 : ℕ := ⌊(M.d 0 4 - M.d 0 3)⌋₊ - 1
  have hnonneg02 : 0 ≤ (M.d 0 4 - M.d 0 3) := hrow_nonneg0 (M.d 0 4 - M.d 0 3) (by simp)
  have hscore02a : (0 : ℝ) ≤ s02 := Nat.cast_nonneg s02
  have hbridge02 := score_gap_dichotomy (M.d 0 4 - M.d 0 3) hnonneg02
  change (s02 = 0 ∧ (M.d 0 4 - M.d 0 3) < 2) ∨ (1 ≤ s02 ∧ (s02 : ℝ)+1 ≤ (M.d 0 4 - M.d 0 3) ∧ (M.d 0 4 - M.d 0 3) < (s02 : ℝ)+2) at hbridge02
  let s03 : ℕ := ⌊(M.d 0 2 - M.d 0 4)⌋₊ - 1
  have hnonneg03 : 0 ≤ (M.d 0 2 - M.d 0 4) := hrow_nonneg0 (M.d 0 2 - M.d 0 4) (by simp)
  have hscore03a : (0 : ℝ) ≤ s03 := Nat.cast_nonneg s03
  have hbridge03 := score_gap_dichotomy (M.d 0 2 - M.d 0 4) hnonneg03
  change (s03 = 0 ∧ (M.d 0 2 - M.d 0 4) < 2) ∨ (1 ≤ s03 ∧ (s03 : ℝ)+1 ≤ (M.d 0 2 - M.d 0 4) ∧ (M.d 0 2 - M.d 0 4) < (s03 : ℝ)+2) at hbridge03
  let s04 : ℕ := ⌊(M.theta 0 + (5 + M.delta) - M.d 0 2)⌋₊ - 1
  have hnonneg04 : 0 ≤ (M.theta 0 + (5 + M.delta) - M.d 0 2) := hrow_nonneg0 (M.theta 0 + (5 + M.delta) - M.d 0 2) (by simp)
  have hscore04a : (0 : ℝ) ≤ s04 := Nat.cast_nonneg s04
  have hbridge04 := score_gap_dichotomy (M.theta 0 + (5 + M.delta) - M.d 0 2) hnonneg04
  change (s04 = 0 ∧ (M.theta 0 + (5 + M.delta) - M.d 0 2) < 2) ∨ (1 ≤ s04 ∧ (s04 : ℝ)+1 ≤ (M.theta 0 + (5 + M.delta) - M.d 0 2) ∧ (M.theta 0 + (5 + M.delta) - M.d 0 2) < (s04 : ℝ)+2) at hbridge04
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
  have hsort1 : ([M.d 0 1, M.d 1 4, M.d 1 3, M.d 1 2] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp1 := M.row_perm 1
  have hcanon10 : M.d 1 0 = M.d 0 1 := M.symm 1 0 (by decide)
  have he1 : (((List.finRange 5).erase (1 : Fin 5)).map (M.d 1)) = [M.d 0 1, M.d 1 2, M.d 1 3, M.d 1 4] := by
    norm_num [List.finRange, List.ofFn_succ, hcanon10]
  rw [he1] at hp1
  have hperm1 := hp1.trans ((((((List.Perm.swap (M.d 1 4) (M.d 1 3) []).cons (M.d 1 2)).cons (M.d 0 1)).trans ((List.Perm.swap (M.d 1 4) (M.d 1 2) [M.d 1 3]).cons (M.d 0 1))).trans (((List.Perm.swap (M.d 1 3) (M.d 1 2) []).cons (M.d 1 4)).cons (M.d 0 1))))
  have hrow1 : M.rowxs 1 = [M.d 0 1, M.d 1 4, M.d 1 3, M.d 1 2] := hperm1.eq_of_pairwise' (M.row_sorted 1) hsort1
  have hrow_nonneg1 := SmallScoreGapBounds.model_gaps_nonneg M 1
  simp only [SmallScoreGapBounds.modelGaps, hrow1, StrongGapBudget.linearGaps] at hrow_nonneg1
  norm_num only [Nat.cast_ofNat] at hrow_nonneg1
  let s10 : ℕ := ⌊(M.d 0 1 - M.theta 1)⌋₊ - 1
  have hnonneg10 : 0 ≤ (M.d 0 1 - M.theta 1) := hrow_nonneg1 (M.d 0 1 - M.theta 1) (by simp)
  have hscore10a : (0 : ℝ) ≤ s10 := Nat.cast_nonneg s10
  have hbridge10 := score_gap_dichotomy (M.d 0 1 - M.theta 1) hnonneg10
  change (s10 = 0 ∧ (M.d 0 1 - M.theta 1) < 2) ∨ (1 ≤ s10 ∧ (s10 : ℝ)+1 ≤ (M.d 0 1 - M.theta 1) ∧ (M.d 0 1 - M.theta 1) < (s10 : ℝ)+2) at hbridge10
  let s11 : ℕ := ⌊(M.d 1 4 - M.d 0 1)⌋₊ - 1
  have hnonneg11 : 0 ≤ (M.d 1 4 - M.d 0 1) := hrow_nonneg1 (M.d 1 4 - M.d 0 1) (by simp)
  have hscore11a : (0 : ℝ) ≤ s11 := Nat.cast_nonneg s11
  have hbridge11 := score_gap_dichotomy (M.d 1 4 - M.d 0 1) hnonneg11
  change (s11 = 0 ∧ (M.d 1 4 - M.d 0 1) < 2) ∨ (1 ≤ s11 ∧ (s11 : ℝ)+1 ≤ (M.d 1 4 - M.d 0 1) ∧ (M.d 1 4 - M.d 0 1) < (s11 : ℝ)+2) at hbridge11
  let s12 : ℕ := ⌊(M.d 1 3 - M.d 1 4)⌋₊ - 1
  have hnonneg12 : 0 ≤ (M.d 1 3 - M.d 1 4) := hrow_nonneg1 (M.d 1 3 - M.d 1 4) (by simp)
  have hscore12a : (0 : ℝ) ≤ s12 := Nat.cast_nonneg s12
  have hbridge12 := score_gap_dichotomy (M.d 1 3 - M.d 1 4) hnonneg12
  change (s12 = 0 ∧ (M.d 1 3 - M.d 1 4) < 2) ∨ (1 ≤ s12 ∧ (s12 : ℝ)+1 ≤ (M.d 1 3 - M.d 1 4) ∧ (M.d 1 3 - M.d 1 4) < (s12 : ℝ)+2) at hbridge12
  let s13 : ℕ := ⌊(M.d 1 2 - M.d 1 3)⌋₊ - 1
  have hnonneg13 : 0 ≤ (M.d 1 2 - M.d 1 3) := hrow_nonneg1 (M.d 1 2 - M.d 1 3) (by simp)
  have hscore13a : (0 : ℝ) ≤ s13 := Nat.cast_nonneg s13
  have hbridge13 := score_gap_dichotomy (M.d 1 2 - M.d 1 3) hnonneg13
  change (s13 = 0 ∧ (M.d 1 2 - M.d 1 3) < 2) ∨ (1 ≤ s13 ∧ (s13 : ℝ)+1 ≤ (M.d 1 2 - M.d 1 3) ∧ (M.d 1 2 - M.d 1 3) < (s13 : ℝ)+2) at hbridge13
  let s14 : ℕ := ⌊(M.theta 1 + (5 + M.delta) - M.d 1 2)⌋₊ - 1
  have hnonneg14 : 0 ≤ (M.theta 1 + (5 + M.delta) - M.d 1 2) := hrow_nonneg1 (M.theta 1 + (5 + M.delta) - M.d 1 2) (by simp)
  have hscore14a : (0 : ℝ) ≤ s14 := Nat.cast_nonneg s14
  have hbridge14 := score_gap_dichotomy (M.theta 1 + (5 + M.delta) - M.d 1 2) hnonneg14
  change (s14 = 0 ∧ (M.theta 1 + (5 + M.delta) - M.d 1 2) < 2) ∨ (1 ≤ s14 ∧ (s14 : ℝ)+1 ≤ (M.theta 1 + (5 + M.delta) - M.d 1 2) ∧ (M.theta 1 + (5 + M.delta) - M.d 1 2) < (s14 : ℝ)+2) at hbridge14
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
  have hsort3 : ([M.d 2 3, M.d 0 3, M.d 3 4, M.d 1 3] : List ℝ).Pairwise (· ≤ ·) := by
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
  have hperm3 := hp3.trans (((((List.Perm.swap (M.d 2 3) (M.d 1 3) [M.d 3 4]).cons (M.d 0 3)).trans (List.Perm.swap (M.d 2 3) (M.d 0 3) [M.d 1 3, M.d 3 4])).trans (((List.Perm.swap (M.d 3 4) (M.d 1 3) []).cons (M.d 0 3)).cons (M.d 2 3))))
  have hrow3 : M.rowxs 3 = [M.d 2 3, M.d 0 3, M.d 3 4, M.d 1 3] := hperm3.eq_of_pairwise' (M.row_sorted 3) hsort3
  have hrow_nonneg3 := SmallScoreGapBounds.model_gaps_nonneg M 3
  simp only [SmallScoreGapBounds.modelGaps, hrow3, StrongGapBudget.linearGaps] at hrow_nonneg3
  norm_num only [Nat.cast_ofNat] at hrow_nonneg3
  let s30 : ℕ := ⌊(M.d 2 3 - M.theta 3)⌋₊ - 1
  have hnonneg30 : 0 ≤ (M.d 2 3 - M.theta 3) := hrow_nonneg3 (M.d 2 3 - M.theta 3) (by simp)
  have hscore30a : (0 : ℝ) ≤ s30 := Nat.cast_nonneg s30
  have hbridge30 := score_gap_dichotomy (M.d 2 3 - M.theta 3) hnonneg30
  change (s30 = 0 ∧ (M.d 2 3 - M.theta 3) < 2) ∨ (1 ≤ s30 ∧ (s30 : ℝ)+1 ≤ (M.d 2 3 - M.theta 3) ∧ (M.d 2 3 - M.theta 3) < (s30 : ℝ)+2) at hbridge30
  let s31 : ℕ := ⌊(M.d 0 3 - M.d 2 3)⌋₊ - 1
  have hnonneg31 : 0 ≤ (M.d 0 3 - M.d 2 3) := hrow_nonneg3 (M.d 0 3 - M.d 2 3) (by simp)
  have hscore31a : (0 : ℝ) ≤ s31 := Nat.cast_nonneg s31
  have hbridge31 := score_gap_dichotomy (M.d 0 3 - M.d 2 3) hnonneg31
  change (s31 = 0 ∧ (M.d 0 3 - M.d 2 3) < 2) ∨ (1 ≤ s31 ∧ (s31 : ℝ)+1 ≤ (M.d 0 3 - M.d 2 3) ∧ (M.d 0 3 - M.d 2 3) < (s31 : ℝ)+2) at hbridge31
  let s32 : ℕ := ⌊(M.d 3 4 - M.d 0 3)⌋₊ - 1
  have hnonneg32 : 0 ≤ (M.d 3 4 - M.d 0 3) := hrow_nonneg3 (M.d 3 4 - M.d 0 3) (by simp)
  have hscore32a : (0 : ℝ) ≤ s32 := Nat.cast_nonneg s32
  have hbridge32 := score_gap_dichotomy (M.d 3 4 - M.d 0 3) hnonneg32
  change (s32 = 0 ∧ (M.d 3 4 - M.d 0 3) < 2) ∨ (1 ≤ s32 ∧ (s32 : ℝ)+1 ≤ (M.d 3 4 - M.d 0 3) ∧ (M.d 3 4 - M.d 0 3) < (s32 : ℝ)+2) at hbridge32
  let s33 : ℕ := ⌊(M.d 1 3 - M.d 3 4)⌋₊ - 1
  have hnonneg33 : 0 ≤ (M.d 1 3 - M.d 3 4) := hrow_nonneg3 (M.d 1 3 - M.d 3 4) (by simp)
  have hscore33a : (0 : ℝ) ≤ s33 := Nat.cast_nonneg s33
  have hbridge33 := score_gap_dichotomy (M.d 1 3 - M.d 3 4) hnonneg33
  change (s33 = 0 ∧ (M.d 1 3 - M.d 3 4) < 2) ∨ (1 ≤ s33 ∧ (s33 : ℝ)+1 ≤ (M.d 1 3 - M.d 3 4) ∧ (M.d 1 3 - M.d 3 4) < (s33 : ℝ)+2) at hbridge33
  let s34 : ℕ := ⌊(M.theta 3 + (5 + M.delta) - M.d 1 3)⌋₊ - 1
  have hnonneg34 : 0 ≤ (M.theta 3 + (5 + M.delta) - M.d 1 3) := hrow_nonneg3 (M.theta 3 + (5 + M.delta) - M.d 1 3) (by simp)
  have hscore34a : (0 : ℝ) ≤ s34 := Nat.cast_nonneg s34
  have hbridge34 := score_gap_dichotomy (M.theta 3 + (5 + M.delta) - M.d 1 3) hnonneg34
  change (s34 = 0 ∧ (M.theta 3 + (5 + M.delta) - M.d 1 3) < 2) ∨ (1 ≤ s34 ∧ (s34 : ℝ)+1 ≤ (M.theta 3 + (5 + M.delta) - M.d 1 3) ∧ (M.theta 3 + (5 + M.delta) - M.d 1 3) < (s34 : ℝ)+2) at hbridge34
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
  have hsort4 : ([M.d 2 4, M.d 0 4, M.d 3 4, M.d 1 4] : List ℝ).Pairwise (· ≤ ·) := by
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
  have hperm4 := hp4.trans (((((List.Perm.swap (M.d 2 4) (M.d 1 4) [M.d 3 4]).cons (M.d 0 4)).trans (List.Perm.swap (M.d 2 4) (M.d 0 4) [M.d 1 4, M.d 3 4])).trans (((List.Perm.swap (M.d 3 4) (M.d 1 4) []).cons (M.d 0 4)).cons (M.d 2 4))))
  have hrow4 : M.rowxs 4 = [M.d 2 4, M.d 0 4, M.d 3 4, M.d 1 4] := hperm4.eq_of_pairwise' (M.row_sorted 4) hsort4
  have hrow_nonneg4 := SmallScoreGapBounds.model_gaps_nonneg M 4
  simp only [SmallScoreGapBounds.modelGaps, hrow4, StrongGapBudget.linearGaps] at hrow_nonneg4
  norm_num only [Nat.cast_ofNat] at hrow_nonneg4
  let s40 : ℕ := ⌊(M.d 2 4 - M.theta 4)⌋₊ - 1
  have hnonneg40 : 0 ≤ (M.d 2 4 - M.theta 4) := hrow_nonneg4 (M.d 2 4 - M.theta 4) (by simp)
  have hscore40a : (0 : ℝ) ≤ s40 := Nat.cast_nonneg s40
  have hbridge40 := score_gap_dichotomy (M.d 2 4 - M.theta 4) hnonneg40
  change (s40 = 0 ∧ (M.d 2 4 - M.theta 4) < 2) ∨ (1 ≤ s40 ∧ (s40 : ℝ)+1 ≤ (M.d 2 4 - M.theta 4) ∧ (M.d 2 4 - M.theta 4) < (s40 : ℝ)+2) at hbridge40
  let s41 : ℕ := ⌊(M.d 0 4 - M.d 2 4)⌋₊ - 1
  have hnonneg41 : 0 ≤ (M.d 0 4 - M.d 2 4) := hrow_nonneg4 (M.d 0 4 - M.d 2 4) (by simp)
  have hscore41a : (0 : ℝ) ≤ s41 := Nat.cast_nonneg s41
  have hbridge41 := score_gap_dichotomy (M.d 0 4 - M.d 2 4) hnonneg41
  change (s41 = 0 ∧ (M.d 0 4 - M.d 2 4) < 2) ∨ (1 ≤ s41 ∧ (s41 : ℝ)+1 ≤ (M.d 0 4 - M.d 2 4) ∧ (M.d 0 4 - M.d 2 4) < (s41 : ℝ)+2) at hbridge41
  let s42 : ℕ := ⌊(M.d 3 4 - M.d 0 4)⌋₊ - 1
  have hnonneg42 : 0 ≤ (M.d 3 4 - M.d 0 4) := hrow_nonneg4 (M.d 3 4 - M.d 0 4) (by simp)
  have hscore42a : (0 : ℝ) ≤ s42 := Nat.cast_nonneg s42
  have hbridge42 := score_gap_dichotomy (M.d 3 4 - M.d 0 4) hnonneg42
  change (s42 = 0 ∧ (M.d 3 4 - M.d 0 4) < 2) ∨ (1 ≤ s42 ∧ (s42 : ℝ)+1 ≤ (M.d 3 4 - M.d 0 4) ∧ (M.d 3 4 - M.d 0 4) < (s42 : ℝ)+2) at hbridge42
  let s43 : ℕ := ⌊(M.d 1 4 - M.d 3 4)⌋₊ - 1
  have hnonneg43 : 0 ≤ (M.d 1 4 - M.d 3 4) := hrow_nonneg4 (M.d 1 4 - M.d 3 4) (by simp)
  have hscore43a : (0 : ℝ) ≤ s43 := Nat.cast_nonneg s43
  have hbridge43 := score_gap_dichotomy (M.d 1 4 - M.d 3 4) hnonneg43
  change (s43 = 0 ∧ (M.d 1 4 - M.d 3 4) < 2) ∨ (1 ≤ s43 ∧ (s43 : ℝ)+1 ≤ (M.d 1 4 - M.d 3 4) ∧ (M.d 1 4 - M.d 3 4) < (s43 : ℝ)+2) at hbridge43
  let s44 : ℕ := ⌊(M.theta 4 + (5 + M.delta) - M.d 1 4)⌋₊ - 1
  have hnonneg44 : 0 ≤ (M.theta 4 + (5 + M.delta) - M.d 1 4) := hrow_nonneg4 (M.theta 4 + (5 + M.delta) - M.d 1 4) (by simp)
  have hscore44a : (0 : ℝ) ≤ s44 := Nat.cast_nonneg s44
  have hbridge44 := score_gap_dichotomy (M.theta 4 + (5 + M.delta) - M.d 1 4) hnonneg44
  change (s44 = 0 ∧ (M.theta 4 + (5 + M.delta) - M.d 1 4) < 2) ∨ (1 ≤ s44 ∧ (s44 : ℝ)+1 ≤ (M.theta 4 + (5 + M.delta) - M.d 1 4) ∧ (M.theta 4 + (5 + M.delta) - M.d 1 4) < (s44 : ℝ)+2) at hbridge44
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
            linarith only [hgap01a, hgap03a, hgap02a, hsum0, hgap04a, hgap00a]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            linarith only [ht12, hgap04b, hgap01a, hgap02a, hdelta1, hgap00a, hc23a, htr234b, hgap03a, htr024a, hsum0, ht01]
        ·
          have hgap03a : (1 : ℝ) ≤ s03 := by exact_mod_cast hpositive03
          rcases hbridge04 with ⟨hzero04, hgap04b⟩ | ⟨hpositive04, hgap04b, hgap04c⟩
          ·
            have hgap04a : (s04 : ℝ) = 0 := by exact_mod_cast hzero04
            linarith only [hc02b, htr034b, hc23a, hgap04a, hdelta1, hgap02a, hgap03b, hgap01a, htr023b, hsum0, hgap00a]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            linarith only [hgap04b, hc23a, hgap03b, htr023b, hgap02a, htr034b, hdelta1, hgap00a, hgap01a, ht12, hsum0, ht01]
      ·
        have hgap02a : (1 : ℝ) ≤ s02 := by exact_mod_cast hpositive02
        rcases hbridge03 with ⟨hzero03, hgap03b⟩ | ⟨hpositive03, hgap03b, hgap03c⟩
        ·
          have hgap03a : (s03 : ℝ) = 0 := by exact_mod_cast hzero03
          rcases hbridge04 with ⟨hzero04, hgap04b⟩ | ⟨hpositive04, hgap04b, hgap04c⟩
          ·
            have hgap04a : (s04 : ℝ) = 0 := by exact_mod_cast hzero04
            linarith only [hgap03a, hgap00a, hc23a, hgap04a, hgap02b, hdelta1, hgap01a, hsum0, htr024c, hc02b, htr023b]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            linarith only [hc23a, hdelta1, ht01, hgap01a, ht12, hgap04b, htr024c, hgap02b, hgap03a, hsum0, htr023b, hgap00a]
        ·
          have hgap03a : (1 : ℝ) ≤ s03 := by exact_mod_cast hpositive03
          linarith only [htr023b, hc23a, hgap02b, hgap02a, hgap03b, hc02b, hdelta1, hgap03a]
    ·
      have hgap01a : (1 : ℝ) ≤ s01 := by exact_mod_cast hpositive01
      rcases hbridge30 with ⟨hzero30, hgap30b⟩ | ⟨hpositive30, hgap30b, hgap30c⟩
      ·
        have hgap30a : (s30 : ℝ) = 0 := by exact_mod_cast hzero30
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
                linarith only [hgap33a, hsum3, hgap32a, hgap31a, hgap34a, hgap30a]
              ·
                have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                linarith only [hgap01b, htr034a, hgap01a, hgap32a, hgap30a, ht34, htr134a, hgap33a, hsum3, hdelta1, ht4b, hgap31a, hgap34b, hc01a, ht0a]
            ·
              have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
              linarith only [hgap01b, hc12b, hgap33b, ht0a, htr034a, ht4b, ht23, hc01a, hdelta1, hgap33a, htr123c, ht34, hgap01a]
          ·
            have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
            linarith only [hc01a, hgap01a, htr134a, hdelta1, htr123c, hgap01b, hgap32a, ht0a, hc12b, ht23, ht4b, ht34, hgap32b]
        ·
          have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
          linarith only [htr134a, hc12b, hc23a, hdelta1, hgap31b, hgap31a, htr123c, htr034a]
      ·
        have hgap30a : (1 : ℝ) ≤ s30 := by exact_mod_cast hpositive30
        rcases hbridge31 with ⟨hzero31, hgap31b⟩ | ⟨hpositive31, hgap31b, hgap31c⟩
        ·
          have hgap31a : (s31 : ℝ) = 0 := by exact_mod_cast hzero31
          rcases hbridge02 with ⟨hzero02, hgap02b⟩ | ⟨hpositive02, hgap02b, hgap02c⟩
          ·
            have hgap02a : (s02 : ℝ) = 0 := by exact_mod_cast hzero02
            rcases hbridge32 with ⟨hzero32, hgap32b⟩ | ⟨hpositive32, hgap32b, hgap32c⟩
            ·
              have hgap32a : (s32 : ℝ) = 0 := by exact_mod_cast hzero32
              rcases hbridge33 with ⟨hzero33, hgap33b⟩ | ⟨hpositive33, hgap33b, hgap33c⟩
              ·
                have hgap33a : (s33 : ℝ) = 0 := by exact_mod_cast hzero33
                rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                ·
                  have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
                  linarith only [hgap34a, hc12b, htr034a, hgap32a, hgap31a, htr134a, hsum3, ht23, htr123c, hgap30b, htr023b, hgap33a, hdelta1]
                ·
                  have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                  linarith only [ht0a, hdelta1, hc01a, hgap34a, hgap01b, ht4b, htr034a, htr134a, hgap01a, hgap34b, ht34]
              ·
                have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                linarith only [hgap01a, hc01a, hgap01b, ht0a, hgap33a, hdelta1, htr034a, htr123c, ht34, hgap33b, hc12b, ht23, ht4b]
            ·
              have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
              linarith only [ht23, hgap32a, hgap01a, htr134a, hgap01b, ht4b, ht0a, hc12b, htr123c, hgap32b, ht34, hc01a, hdelta1]
          ·
            have hgap02a : (1 : ℝ) ≤ s02 := by exact_mod_cast hpositive02
            linarith only [htr134a, hgap01a, hgap01b, hgap02a, hc13b, htr034c, hgap02b, hc01a, ht4b, ht34, ht0a, hdelta1]
        ·
          have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
          linarith only [htr134a, hgap31a, hc12b, htr034a, hdelta1, hc23a, htr123c, hgap31b]
  ·
    have hgap00a : (1 : ℝ) ≤ s00 := by exact_mod_cast hpositive00
    rcases hbridge30 with ⟨hzero30, hgap30b⟩ | ⟨hpositive30, hgap30b, hgap30c⟩
    ·
      have hgap30a : (s30 : ℝ) = 0 := by exact_mod_cast hzero30
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
              linarith only [hgap33a, hgap34a, hsum3, hgap30a, hgap31a, hgap32a]
            ·
              have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
              linarith only [hgap33a, hgap32a, htr034a, htr013b, ht34, hdelta1, ht4b, hgap30a, hsum3, hgap00a, hgap31a, ht0a, hgap34b, hgap00b, htr134a]
          ·
            have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
            rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
            ·
              have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
              linarith only [hgap34a, hdelta1, hgap00b, hc12b, htr123c, hgap00a, hgap31a, hgap32a, ht23, hgap33b, hsum3, ht34, ht0a, htr034a, hgap30a, htr013b, ht4b]
            ·
              have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
              linarith only [hgap33b, hgap34b, ht4b, hdelta1, ht34, hgap33a, htr013b, ht0a, hgap34a, htr034a, hgap00a, hgap00b]
        ·
          have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
          rcases hbridge33 with ⟨hzero33, hgap33b⟩ | ⟨hpositive33, hgap33b, hgap33c⟩
          ·
            have hgap33a : (s33 : ℝ) = 0 := by exact_mod_cast hzero33
            rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
            ·
              have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
              linarith only [hgap00a, hgap34a, hgap00b, ht34, ht0a, htr013b, hgap33a, htr134a, hc13b, ht4b, hgap31a, hgap30a, hsum3, hdelta1, hgap32b]
            ·
              have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
              linarith only [ht4b, hgap00a, hgap32a, htr134a, ht34, hgap34a, hgap34b, hdelta1, htr013b, hgap32b, ht0a, hgap00b]
          ·
            have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
            linarith only [hgap32a, htr013b, hdelta1, hgap00a, hc12b, hgap33a, ht4b, htr123c, hgap33b, ht23, ht0a, hgap00b, hgap32b, ht34]
      ·
        have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
        linarith only [hc12b, htr134a, hgap31a, hdelta1, hc23a, htr034a, htr123c, hgap31b]
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
              linarith only [hgap33a, hgap32a, hc13b, htr034a, htr023b, hsum3, htr134a, hgap34a, hdelta1, hgap31a, hgap30b]
            ·
              have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
              linarith only [htr134a, hgap34a, hdelta1, hgap30a, htr034a, hgap34b, hgap30b, htr023b]
          ·
            have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
            linarith only [hdelta1, hc12b, hgap30b, htr034a, htr023b, hgap30a, hgap33b, ht23, hgap33a, htr123c]
        ·
          have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
          linarith only [htr123c, hgap30a, hgap32a, hgap32b, htr023b, hdelta1, htr134a, hc12b, hgap30b, ht23]
      ·
        have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
        linarith only [htr034a, hgap30a, hgap31a, ht23, htr134a, hc12b, hgap31b, hgap30b, htr123c, hdelta1]

#print axioms n5_between_mask472
end Jsp404.SixExactFloorKernel
