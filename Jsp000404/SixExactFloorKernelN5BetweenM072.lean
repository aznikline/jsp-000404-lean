import Jsp000404.SixExactFloorKernelPrimitives

/-! Representative exact-score certificate. A fixed orientation is an explicit
hypothesis only for this probe; public wrappers must split every triangle arm. -/
namespace Jsp404.SixExactFloorKernel

set_option maxHeartbeats 16000000 in
theorem n5_between_mask072 (M : SixModelCompression.ModelSix 5)
    (hhigh : (1/2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    (htri012 : M.d 0 1+1 ≤ M.d 1 2 ∧ M.d 0 1 < M.d 0 2 ∧ M.d 0 2 < M.d 1 2)
    (htri013 : M.d 0 1+1 ≤ M.d 1 3 ∧ M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (htri014 : M.d 0 1+1 ≤ M.d 1 4 ∧ M.d 0 1 < M.d 0 4 ∧ M.d 0 4 < M.d 1 4)
    (htri023 : M.d 2 3+1 ≤ M.d 0 2 ∧ M.d 2 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 2)
    (htri024 : M.d 0 2+1 ≤ M.d 2 4 ∧ M.d 0 2 < M.d 0 4 ∧ M.d 0 4 < M.d 2 4)
    (htri034 : M.d 0 3+1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (htri123 : M.d 2 3+1 ≤ M.d 1 2 ∧ M.d 2 3 < M.d 1 3 ∧ M.d 1 3 < M.d 1 2)
    (htri124 : M.d 1 2+1 ≤ M.d 2 4 ∧ M.d 1 2 < M.d 1 4 ∧ M.d 1 4 < M.d 2 4)
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
  have hsort0 : ([M.d 0 1, M.d 0 3, M.d 0 2, M.d 0 4] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp0 := M.row_perm 0
  have he0 : (((List.finRange 5).erase (0 : Fin 5)).map (M.d 0)) = [M.d 0 1, M.d 0 2, M.d 0 3, M.d 0 4] := by
    norm_num [List.finRange, List.ofFn_succ]
  rw [he0] at hp0
  have hperm0 := hp0.trans (((List.Perm.swap (M.d 0 3) (M.d 0 2) [M.d 0 4]).cons (M.d 0 1)))
  have hrow0 : M.rowxs 0 = [M.d 0 1, M.d 0 3, M.d 0 2, M.d 0 4] := hperm0.eq_of_pairwise' (M.row_sorted 0) hsort0
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
  let s02 : ℕ := ⌊(M.d 0 2 - M.d 0 3)⌋₊ - 1
  have hnonneg02 : 0 ≤ (M.d 0 2 - M.d 0 3) := hrow_nonneg0 (M.d 0 2 - M.d 0 3) (by simp)
  have hscore02a : (0 : ℝ) ≤ s02 := Nat.cast_nonneg s02
  have hbridge02 := score_gap_dichotomy (M.d 0 2 - M.d 0 3) hnonneg02
  change (s02 = 0 ∧ (M.d 0 2 - M.d 0 3) < 2) ∨ (1 ≤ s02 ∧ (s02 : ℝ)+1 ≤ (M.d 0 2 - M.d 0 3) ∧ (M.d 0 2 - M.d 0 3) < (s02 : ℝ)+2) at hbridge02
  let s03 : ℕ := ⌊(M.d 0 4 - M.d 0 2)⌋₊ - 1
  have hnonneg03 : 0 ≤ (M.d 0 4 - M.d 0 2) := hrow_nonneg0 (M.d 0 4 - M.d 0 2) (by simp)
  have hscore03a : (0 : ℝ) ≤ s03 := Nat.cast_nonneg s03
  have hbridge03 := score_gap_dichotomy (M.d 0 4 - M.d 0 2) hnonneg03
  change (s03 = 0 ∧ (M.d 0 4 - M.d 0 2) < 2) ∨ (1 ≤ s03 ∧ (s03 : ℝ)+1 ≤ (M.d 0 4 - M.d 0 2) ∧ (M.d 0 4 - M.d 0 2) < (s03 : ℝ)+2) at hbridge03
  let s04 : ℕ := ⌊(M.theta 0 + (5 + M.delta) - M.d 0 4)⌋₊ - 1
  have hnonneg04 : 0 ≤ (M.theta 0 + (5 + M.delta) - M.d 0 4) := hrow_nonneg0 (M.theta 0 + (5 + M.delta) - M.d 0 4) (by simp)
  have hscore04a : (0 : ℝ) ≤ s04 := Nat.cast_nonneg s04
  have hbridge04 := score_gap_dichotomy (M.theta 0 + (5 + M.delta) - M.d 0 4) hnonneg04
  change (s04 = 0 ∧ (M.theta 0 + (5 + M.delta) - M.d 0 4) < 2) ∨ (1 ≤ s04 ∧ (s04 : ℝ)+1 ≤ (M.theta 0 + (5 + M.delta) - M.d 0 4) ∧ (M.theta 0 + (5 + M.delta) - M.d 0 4) < (s04 : ℝ)+2) at hbridge04
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
  have hsort1 : ([M.d 0 1, M.d 1 3, M.d 1 2, M.d 1 4] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp1 := M.row_perm 1
  have hcanon10 : M.d 1 0 = M.d 0 1 := M.symm 1 0 (by decide)
  have he1 : (((List.finRange 5).erase (1 : Fin 5)).map (M.d 1)) = [M.d 0 1, M.d 1 2, M.d 1 3, M.d 1 4] := by
    norm_num [List.finRange, List.ofFn_succ, hcanon10]
  rw [he1] at hp1
  have hperm1 := hp1.trans (((List.Perm.swap (M.d 1 3) (M.d 1 2) [M.d 1 4]).cons (M.d 0 1)))
  have hrow1 : M.rowxs 1 = [M.d 0 1, M.d 1 3, M.d 1 2, M.d 1 4] := hperm1.eq_of_pairwise' (M.row_sorted 1) hsort1
  have hrow_nonneg1 := SmallScoreGapBounds.model_gaps_nonneg M 1
  simp only [SmallScoreGapBounds.modelGaps, hrow1, StrongGapBudget.linearGaps] at hrow_nonneg1
  norm_num only [Nat.cast_ofNat] at hrow_nonneg1
  let s10 : ℕ := ⌊(M.d 0 1 - M.theta 1)⌋₊ - 1
  have hnonneg10 : 0 ≤ (M.d 0 1 - M.theta 1) := hrow_nonneg1 (M.d 0 1 - M.theta 1) (by simp)
  have hscore10a : (0 : ℝ) ≤ s10 := Nat.cast_nonneg s10
  have hbridge10 := score_gap_dichotomy (M.d 0 1 - M.theta 1) hnonneg10
  change (s10 = 0 ∧ (M.d 0 1 - M.theta 1) < 2) ∨ (1 ≤ s10 ∧ (s10 : ℝ)+1 ≤ (M.d 0 1 - M.theta 1) ∧ (M.d 0 1 - M.theta 1) < (s10 : ℝ)+2) at hbridge10
  let s11 : ℕ := ⌊(M.d 1 3 - M.d 0 1)⌋₊ - 1
  have hnonneg11 : 0 ≤ (M.d 1 3 - M.d 0 1) := hrow_nonneg1 (M.d 1 3 - M.d 0 1) (by simp)
  have hscore11a : (0 : ℝ) ≤ s11 := Nat.cast_nonneg s11
  have hbridge11 := score_gap_dichotomy (M.d 1 3 - M.d 0 1) hnonneg11
  change (s11 = 0 ∧ (M.d 1 3 - M.d 0 1) < 2) ∨ (1 ≤ s11 ∧ (s11 : ℝ)+1 ≤ (M.d 1 3 - M.d 0 1) ∧ (M.d 1 3 - M.d 0 1) < (s11 : ℝ)+2) at hbridge11
  let s12 : ℕ := ⌊(M.d 1 2 - M.d 1 3)⌋₊ - 1
  have hnonneg12 : 0 ≤ (M.d 1 2 - M.d 1 3) := hrow_nonneg1 (M.d 1 2 - M.d 1 3) (by simp)
  have hscore12a : (0 : ℝ) ≤ s12 := Nat.cast_nonneg s12
  have hbridge12 := score_gap_dichotomy (M.d 1 2 - M.d 1 3) hnonneg12
  change (s12 = 0 ∧ (M.d 1 2 - M.d 1 3) < 2) ∨ (1 ≤ s12 ∧ (s12 : ℝ)+1 ≤ (M.d 1 2 - M.d 1 3) ∧ (M.d 1 2 - M.d 1 3) < (s12 : ℝ)+2) at hbridge12
  let s13 : ℕ := ⌊(M.d 1 4 - M.d 1 2)⌋₊ - 1
  have hnonneg13 : 0 ≤ (M.d 1 4 - M.d 1 2) := hrow_nonneg1 (M.d 1 4 - M.d 1 2) (by simp)
  have hscore13a : (0 : ℝ) ≤ s13 := Nat.cast_nonneg s13
  have hbridge13 := score_gap_dichotomy (M.d 1 4 - M.d 1 2) hnonneg13
  change (s13 = 0 ∧ (M.d 1 4 - M.d 1 2) < 2) ∨ (1 ≤ s13 ∧ (s13 : ℝ)+1 ≤ (M.d 1 4 - M.d 1 2) ∧ (M.d 1 4 - M.d 1 2) < (s13 : ℝ)+2) at hbridge13
  let s14 : ℕ := ⌊(M.theta 1 + (5 + M.delta) - M.d 1 4)⌋₊ - 1
  have hnonneg14 : 0 ≤ (M.theta 1 + (5 + M.delta) - M.d 1 4) := hrow_nonneg1 (M.theta 1 + (5 + M.delta) - M.d 1 4) (by simp)
  have hscore14a : (0 : ℝ) ≤ s14 := Nat.cast_nonneg s14
  have hbridge14 := score_gap_dichotomy (M.theta 1 + (5 + M.delta) - M.d 1 4) hnonneg14
  change (s14 = 0 ∧ (M.theta 1 + (5 + M.delta) - M.d 1 4) < 2) ∨ (1 ≤ s14 ∧ (s14 : ℝ)+1 ≤ (M.theta 1 + (5 + M.delta) - M.d 1 4) ∧ (M.theta 1 + (5 + M.delta) - M.d 1 4) < (s14 : ℝ)+2) at hbridge14
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
  have hsort3 : ([M.d 2 3, M.d 0 3, M.d 1 3, M.d 3 4] : List ℝ).Pairwise (· ≤ ·) := by
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
  have hperm3 := hp3.trans ((((List.Perm.swap (M.d 2 3) (M.d 1 3) [M.d 3 4]).cons (M.d 0 3)).trans (List.Perm.swap (M.d 2 3) (M.d 0 3) [M.d 1 3, M.d 3 4])))
  have hrow3 : M.rowxs 3 = [M.d 2 3, M.d 0 3, M.d 1 3, M.d 3 4] := hperm3.eq_of_pairwise' (M.row_sorted 3) hsort3
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
  let s32 : ℕ := ⌊(M.d 1 3 - M.d 0 3)⌋₊ - 1
  have hnonneg32 : 0 ≤ (M.d 1 3 - M.d 0 3) := hrow_nonneg3 (M.d 1 3 - M.d 0 3) (by simp)
  have hscore32a : (0 : ℝ) ≤ s32 := Nat.cast_nonneg s32
  have hbridge32 := score_gap_dichotomy (M.d 1 3 - M.d 0 3) hnonneg32
  change (s32 = 0 ∧ (M.d 1 3 - M.d 0 3) < 2) ∨ (1 ≤ s32 ∧ (s32 : ℝ)+1 ≤ (M.d 1 3 - M.d 0 3) ∧ (M.d 1 3 - M.d 0 3) < (s32 : ℝ)+2) at hbridge32
  let s33 : ℕ := ⌊(M.d 3 4 - M.d 1 3)⌋₊ - 1
  have hnonneg33 : 0 ≤ (M.d 3 4 - M.d 1 3) := hrow_nonneg3 (M.d 3 4 - M.d 1 3) (by simp)
  have hscore33a : (0 : ℝ) ≤ s33 := Nat.cast_nonneg s33
  have hbridge33 := score_gap_dichotomy (M.d 3 4 - M.d 1 3) hnonneg33
  change (s33 = 0 ∧ (M.d 3 4 - M.d 1 3) < 2) ∨ (1 ≤ s33 ∧ (s33 : ℝ)+1 ≤ (M.d 3 4 - M.d 1 3) ∧ (M.d 3 4 - M.d 1 3) < (s33 : ℝ)+2) at hbridge33
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
  have hsort4 : ([M.d 0 4, M.d 1 4, M.d 2 4, M.d 3 4] : List ℝ).Pairwise (· ≤ ·) := by
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
  have hperm4 := hp4.trans (List.Perm.refl [M.d 0 4, M.d 1 4, M.d 2 4, M.d 3 4])
  have hrow4 : M.rowxs 4 = [M.d 0 4, M.d 1 4, M.d 2 4, M.d 3 4] := hperm4.eq_of_pairwise' (M.row_sorted 4) hsort4
  have hrow_nonneg4 := SmallScoreGapBounds.model_gaps_nonneg M 4
  simp only [SmallScoreGapBounds.modelGaps, hrow4, StrongGapBudget.linearGaps] at hrow_nonneg4
  norm_num only [Nat.cast_ofNat] at hrow_nonneg4
  let s40 : ℕ := ⌊(M.d 0 4 - M.theta 4)⌋₊ - 1
  have hnonneg40 : 0 ≤ (M.d 0 4 - M.theta 4) := hrow_nonneg4 (M.d 0 4 - M.theta 4) (by simp)
  have hscore40a : (0 : ℝ) ≤ s40 := Nat.cast_nonneg s40
  have hbridge40 := score_gap_dichotomy (M.d 0 4 - M.theta 4) hnonneg40
  change (s40 = 0 ∧ (M.d 0 4 - M.theta 4) < 2) ∨ (1 ≤ s40 ∧ (s40 : ℝ)+1 ≤ (M.d 0 4 - M.theta 4) ∧ (M.d 0 4 - M.theta 4) < (s40 : ℝ)+2) at hbridge40
  let s41 : ℕ := ⌊(M.d 1 4 - M.d 0 4)⌋₊ - 1
  have hnonneg41 : 0 ≤ (M.d 1 4 - M.d 0 4) := hrow_nonneg4 (M.d 1 4 - M.d 0 4) (by simp)
  have hscore41a : (0 : ℝ) ≤ s41 := Nat.cast_nonneg s41
  have hbridge41 := score_gap_dichotomy (M.d 1 4 - M.d 0 4) hnonneg41
  change (s41 = 0 ∧ (M.d 1 4 - M.d 0 4) < 2) ∨ (1 ≤ s41 ∧ (s41 : ℝ)+1 ≤ (M.d 1 4 - M.d 0 4) ∧ (M.d 1 4 - M.d 0 4) < (s41 : ℝ)+2) at hbridge41
  let s42 : ℕ := ⌊(M.d 2 4 - M.d 1 4)⌋₊ - 1
  have hnonneg42 : 0 ≤ (M.d 2 4 - M.d 1 4) := hrow_nonneg4 (M.d 2 4 - M.d 1 4) (by simp)
  have hscore42a : (0 : ℝ) ≤ s42 := Nat.cast_nonneg s42
  have hbridge42 := score_gap_dichotomy (M.d 2 4 - M.d 1 4) hnonneg42
  change (s42 = 0 ∧ (M.d 2 4 - M.d 1 4) < 2) ∨ (1 ≤ s42 ∧ (s42 : ℝ)+1 ≤ (M.d 2 4 - M.d 1 4) ∧ (M.d 2 4 - M.d 1 4) < (s42 : ℝ)+2) at hbridge42
  let s43 : ℕ := ⌊(M.d 3 4 - M.d 2 4)⌋₊ - 1
  have hnonneg43 : 0 ≤ (M.d 3 4 - M.d 2 4) := hrow_nonneg4 (M.d 3 4 - M.d 2 4) (by simp)
  have hscore43a : (0 : ℝ) ≤ s43 := Nat.cast_nonneg s43
  have hbridge43 := score_gap_dichotomy (M.d 3 4 - M.d 2 4) hnonneg43
  change (s43 = 0 ∧ (M.d 3 4 - M.d 2 4) < 2) ∨ (1 ≤ s43 ∧ (s43 : ℝ)+1 ≤ (M.d 3 4 - M.d 2 4) ∧ (M.d 3 4 - M.d 2 4) < (s43 : ℝ)+2) at hbridge43
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
            linarith only [hgap02a, hgap01a, hgap03a, hgap00a, hsum0, hgap04a]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            linarith only [hgap01a, htr023a, hgap00a, ht01, hgap03a, hdelta1, htr024b, ht12, hgap04b, hgap02a, hsum0, hc23a]
        ·
          have hgap03a : (1 : ℝ) ≤ s03 := by exact_mod_cast hpositive03
          rcases hbridge04 with ⟨hzero04, hgap04b⟩ | ⟨hpositive04, hgap04b, hgap04c⟩
          ·
            have hgap04a : (s04 : ℝ) = 0 := by exact_mod_cast hzero04
            linarith only [hsum0, ht0a, hgap02a, ht4b, htr023a, ht12, hgap00a, hdelta1, hc23a, hgap01a, hgap04a, ht01, hc04b, hgap03b]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            linarith only [hdelta1, htr023a, ht12, hgap00a, hgap02a, hgap01a, hgap04b, hgap03b, hsum0, ht01, hc23a]
      ·
        have hgap02a : (1 : ℝ) ≤ s02 := by exact_mod_cast hpositive02
        rcases hbridge03 with ⟨hzero03, hgap03b⟩ | ⟨hpositive03, hgap03b, hgap03c⟩
        ·
          have hgap03a : (s03 : ℝ) = 0 := by exact_mod_cast hzero03
          rcases hbridge04 with ⟨hzero04, hgap04b⟩ | ⟨hpositive04, hgap04b, hgap04c⟩
          ·
            have hgap04a : (s04 : ℝ) = 0 := by exact_mod_cast hzero04
            linarith only [hdelta1, hc02b, hc23a, hsum0, htr023b, hgap00a, hgap03a, hgap01a, hgap02b, hgap04a]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            linarith only [hgap04b, hc23a, hsum0, hgap02b, hgap00a, ht12, ht01, htr023b, htr024b, hgap01a, hgap03a, hdelta1]
        ·
          have hgap03a : (1 : ℝ) ≤ s03 := by exact_mod_cast hpositive03
          rcases hbridge04 with ⟨hzero04, hgap04b⟩ | ⟨hpositive04, hgap04b, hgap04c⟩
          ·
            have hgap04a : (s04 : ℝ) = 0 := by exact_mod_cast hzero04
            linarith only [hsum0, hgap01a, hc04b, ht12, htr023b, hgap02b, hgap04a, hc23a, hgap00a, hdelta1, ht01, hgap03b, ht4b, ht0a]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            linarith only [hgap02a, hc23a, ht01, hgap04a, hgap02b, hgap04b, hgap03b, hgap03a, ht12, hdelta1, htr023b]
    ·
      have hgap01a : (1 : ℝ) ≤ s01 := by exact_mod_cast hpositive01
      rcases hbridge02 with ⟨hzero02, hgap02b⟩ | ⟨hpositive02, hgap02b, hgap02c⟩
      ·
        have hgap02a : (s02 : ℝ) = 0 := by exact_mod_cast hzero02
        rcases hbridge03 with ⟨hzero03, hgap03b⟩ | ⟨hpositive03, hgap03b, hgap03c⟩
        ·
          have hgap03a : (s03 : ℝ) = 0 := by exact_mod_cast hzero03
          rcases hbridge04 with ⟨hzero04, hgap04b⟩ | ⟨hpositive04, hgap04b, hgap04c⟩
          ·
            have hgap04a : (s04 : ℝ) = 0 := by exact_mod_cast hzero04
            linarith only [hgap00a, hgap04a, hsum0, hgap03a, htr024a, hgap02a, ht4b, hgap01b, hc01a, hdelta1, hc24b, ht0a, htr023c]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            linarith only [hgap03a, hgap00a, hsum0, hgap02a, hc01a, htr023c, hgap04b, hgap01b, hdelta1, htr024b]
        ·
          have hgap03a : (1 : ℝ) ≤ s03 := by exact_mod_cast hpositive03
          rcases hbridge04 with ⟨hzero04, hgap04b⟩ | ⟨hpositive04, hgap04b, hgap04c⟩
          ·
            have hgap04a : (s04 : ℝ) = 0 := by exact_mod_cast hzero04
            linarith only [hgap02a, hsum0, hc01a, htr023c, hgap01b, hc04b, hgap03b, ht4b, hdelta1, ht0a, hgap00a, hgap04a]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            linarith only [hgap04b, hgap04a, hgap01b, hgap03a, hdelta1, hc01a, htr023c, hgap01a, hgap03b]
      ·
        have hgap02a : (1 : ℝ) ≤ s02 := by exact_mod_cast hpositive02
        linarith only [hgap02b, htr012c, hc24b, ht0a, hgap01a, hgap01b, ht4b, hc01a, htr124a, hdelta1, hgap02a]
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
            linarith only [hgap03a, hgap04a, htr124a, htr234c, hgap00b, ht0a, hsum0, hc34b, hdelta1, htr013a, ht4b, htr123c, hgap02a, hgap01a]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            rcases hbridge11 with ⟨hzero11, hgap11b⟩ | ⟨hpositive11, hgap11b, hgap11c⟩
            ·
              have hgap11a : (s11 : ℝ) = 0 := by exact_mod_cast hzero11
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
                        linarith only [hgap42a, hgap41a, hgap40a, hgap43a, hsum4, hgap44a]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [htr124a, hgap44b, hgap42a, htr234c, hgap00a, hdelta1, hgap41a, hgap00b, ht0a, hsum4, htr123c, hgap40a, ht4b, htr013a, hgap43a]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [htr013a, hgap43b, htr123c, ht0a, hdelta1, hgap00a, hc34b, htr124a, ht4b, hgap00b, hgap43a]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    rcases hbridge30 with ⟨hzero30, hgap30b⟩ | ⟨hpositive30, hgap30b, hgap30c⟩
                    ·
                      have hgap30a : (s30 : ℝ) = 0 := by exact_mod_cast hzero30
                      rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                      ·
                        have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                        rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                        ·
                          have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                          linarith only [hgap40a, hgap44a, htr123c, htr124b, hdelta1, hgap42b, hgap41a, ht0a, hgap00b, hsum4, hgap43a, htr013a, hc24b, hgap00a, ht4b]
                        ·
                          have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                          linarith only [hsum4, hgap00a, hgap43a, hgap42b, hgap41a, hgap44b, htr234c, hgap00b, hgap40a, hdelta1, ht0a, htr013a, htr124b, ht4b, htr123c]
                      ·
                        have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                        linarith only [hdelta1, hgap00a, ht0a, hgap42b, hgap42a, hgap43b, hgap00b, hc34b, htr123c, ht4b, htr124b, hgap43a, htr013a]
                    ·
                      have hgap30a : (1 : ℝ) ≤ s30 := by exact_mod_cast hpositive30
                      linarith only [ht12, ht23, hgap40b, hdelta1, hgap30a, ht0a, ht4b, htr023a, htr024b, hgap30b, ht01]
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
                        linarith only [hgap42a, ht12, ht01, hc23a, ht4b, hgap40a, hgap43a, htr024b, hgap44a, hdelta1, ht0a, hgap41b, hc14b, htr023a, hsum4]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [hc23a, htr024b, hgap43a, hgap42a, ht12, htr023a, hdelta1, htr234c, ht01, hsum4, hgap41b, ht4b, hgap40a, hgap44b, ht0a, htr124c]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [ht4b, hc34b, htr023a, hgap43a, ht12, ht01, hgap41a, hdelta1, htr024b, htr124c, hgap41b, ht0a, hc23a, hgap43b]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    linarith only [ht4b, hc24b, ht0a, htr024b, ht12, hgap41a, hc23a, hgap42a, htr023a, hgap41b, ht01, hdelta1, hgap42b]
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
                        linarith only [hgap03a, hc24b, hgap43a, htr124a, hgap40b, hgap44a, hgap41a, hgap02a, hsum4, hdelta1, hgap01a, htr123c, hsum0, htr013a, hgap00b, hgap42a, hgap04b]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [hgap42a, hgap01a, hgap41a, hgap43a, htr013a, hsum0, htr123c, hdelta1, hgap00b, hgap04b, hgap44b, hgap03a, htr234c, hgap40b, hgap02a, hsum4, htr124a]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [hgap00a, hgap43b, ht0a, hdelta1, hgap00b, ht4b, hc34b, hgap43a, htr124a, htr013a, htr123c]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    rcases hbridge43 with ⟨hzero43, hgap43b⟩ | ⟨hpositive43, hgap43b, hgap43c⟩
                    ·
                      have hgap43a : (s43 : ℝ) = 0 := by exact_mod_cast hzero43
                      rcases hbridge44 with ⟨hzero44, hgap44b⟩ | ⟨hpositive44, hgap44b, hgap44c⟩
                      ·
                        have hgap44a : (s44 : ℝ) = 0 := by exact_mod_cast hzero44
                        linarith only [htr014c, hsum4, hgap41a, hc24b, hgap43a, hgap40b, hgap42b, hgap44a, hdelta1]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [hgap44b, htr123c, hgap42a, htr234c, hdelta1, hgap00a, htr013a, hgap44a, ht4b, htr124b, hgap42b, ht0a, hgap00b]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [htr124b, hgap42b, hgap43a, hgap43b, htr123c, hgap00a, hgap42a, ht4b, htr013a, hgap00b, hc34b, ht0a, hdelta1]
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
                        linarith only [hgap42a, hsum4, hgap44a, hc14b, hgap43a, hgap40b, hdelta1, hgap41b]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [hgap40b, hdelta1, hgap41a, hgap44b, hgap41b, hgap44a, htr124c, hgap40a, htr234c]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [hdelta1, hgap41b, hgap43a, hgap40b, hgap41a, htr124c, hgap40a, hgap43b, hc34b]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    linarith only [hdelta1, hgap41b, hgap40a, hgap40b, hc24b, hgap42b, hgap41a, hgap42a]
            ·
              have hgap11a : (1 : ℝ) ≤ s11 := by exact_mod_cast hpositive11
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
                        linarith only [hgap42a, hgap43a, hgap41a, hsum4, hgap40a, hgap44a]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [hgap44b, hgap00a, hdelta1, ht0a, hgap00b, htr123c, hgap43a, htr234c, ht4b, hgap41a, hgap11a, hgap11b, hgap42a, hgap40a, htr124a, hsum4]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [hdelta1, hgap00b, hgap00a, htr124a, ht0a, htr123c, hgap11b, ht4b, hgap43b, hgap43a, hgap11a, hc34b]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    linarith only [hgap11b, htr234c, hgap00a, hgap00b, ht0a, hgap42b, hdelta1, hc34b, hgap11a, htr124b, htr123c, ht4b, hgap42a]
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
                        linarith only [hc23a, hsum4, hgap42a, hgap44a, htr024b, hdelta1, htr023a, hgap40a, ht0a, hgap43a, hc14b, ht4b, hgap41b, ht12, ht01]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [ht0a, hc23a, hgap44b, htr134c, hgap40a, ht12, hdelta1, hsum4, hgap41b, htr024b, hgap43a, ht01, hgap42a, htr023a, ht4b]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [ht4b, hdelta1, hgap43a, hgap43b, htr123c, hgap00a, hgap00b, htr124a, ht0a, hc34b, hgap11b, hgap11a]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    linarith only [hgap42b, hc23a, hgap42a, hc34b, hdelta1, hgap41b, ht12, ht0a, hgap41a, ht4b, ht01, htr024b, htr234c, htr023a]
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
                        linarith only [hgap43a, htr234c, hsum0, hdelta1, hgap44a, hgap04b, hgap11b, htr124a, hgap01a, hgap00b, hc34b, hgap02a, hgap03a, hgap40b, htr123c, hgap11a, hgap41a, hsum4, hgap42a]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [hgap44b, hdelta1, hgap00b, htr123c, htr124a, ht4b, ht0a, hgap11a, hgap11b, htr234c, hgap00a, hgap44a]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [htr124a, hgap43b, hgap00a, hc34b, hdelta1, hgap11a, hgap43a, hgap11b, hgap00b, ht4b, ht0a, htr123c]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    linarith only [ht0a, ht4b, htr234c, hgap11b, hgap42a, hdelta1, hgap11a, hgap00a, htr123c, hgap42b, hc34b, htr124b, hgap00b]
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
                        linarith only [hgap44a, hgap40b, hgap43a, hgap41b, hdelta1, hc14b, hgap42a, hsum4]
                      ·
                        have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                        linarith only [ht4b, hgap44a, htr123c, hdelta1, hgap11b, ht0a, hgap44b, hgap00a, htr234c, hgap11a, hgap00b, htr124a]
                    ·
                      have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                      linarith only [htr124a, hc34b, hgap11a, hgap43b, hdelta1, hgap43a, hgap00a, ht4b, hgap11b, ht0a, hgap00b, htr123c]
                  ·
                    have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                    linarith only [hgap42a, hgap40b, hgap41a, hgap40a, hgap42b, hdelta1, hgap41b, hc34b, htr234c]
        ·
          have hgap03a : (1 : ℝ) ≤ s03 := by exact_mod_cast hpositive03
          rcases hbridge04 with ⟨hzero04, hgap04b⟩ | ⟨hpositive04, hgap04b, hgap04c⟩
          ·
            have hgap04a : (s04 : ℝ) = 0 := by exact_mod_cast hzero04
            rcases hbridge10 with ⟨hzero10, hgap10b⟩ | ⟨hpositive10, hgap10b, hgap10c⟩
            ·
              have hgap10a : (s10 : ℝ) = 0 := by exact_mod_cast hzero10
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
                        linarith only [hgap34a, hgap32a, hgap33a, hgap31a, hgap30a, hsum3]
                      ·
                        have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                        linarith only [hsum0, hgap34b, hgap02a, hgap30a, hgap00b, hgap33a, hgap04a, htr234c, hgap31a, hsum3, hgap01a, htr012b, ht0a, hgap32a, hgap03b, htr124c, htr014c, hdelta1, ht34, ht4b]
                    ·
                      have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                      rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                      ·
                        have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
                        linarith only [hgap00b, ht0a, hc34b, hgap31a, hsum3, hgap34a, hgap33b, hdelta1, hgap30a, hgap32a, hgap00a, ht4b, htr013a]
                      ·
                        have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                        linarith only [ht4b, hgap03b, htr014c, hdelta1, hgap02a, hsum0, hgap00b, htr012b, hgap34b, hgap34a, ht0a, htr124c, hgap04a, htr234c, hgap01a, ht34]
                  ·
                    have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                    rcases hbridge33 with ⟨hzero33, hgap33b⟩ | ⟨hpositive33, hgap33b, hgap33c⟩
                    ·
                      have hgap33a : (s33 : ℝ) = 0 := by exact_mod_cast hzero33
                      rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                      ·
                        have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
                        linarith only [hgap00a, htr013b, htr124a, hgap33a, ht4b, hdelta1, hsum3, ht0a, hgap31a, hgap30a, hgap34a, hc34b, htr123c, hgap32b, hgap00b, htr234c]
                      ·
                        have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                        linarith only [hgap02a, hdelta1, hsum0, ht0a, htr012b, ht4b, hgap03b, htr124c, hgap04a, htr014c, hgap34a, htr234c, ht34, hgap01a, hgap00b, hgap34b]
                    ·
                      have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                      linarith only [ht0a, hc34b, hdelta1, hgap32b, hgap33b, hgap32a, hgap00a, hgap33a, hgap00b, ht4b, htr013b]
                ·
                  have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
                  linarith only [htr023c, hgap04a, hsum0, hgap01a, ht4b, hgap10b, hgap03b, htr234c, ht0a, hgap00b, htr014c, ht12, htr124c, hgap31a, hc23a, hc34b, hgap31b, hgap02a, hdelta1]
              ·
                have hgap30a : (1 : ℝ) ≤ s30 := by exact_mod_cast hpositive30
                linarith only [ht12, htr234c, hgap03b, hc34b, hgap00b, hgap02a, hgap30a, hgap30b, htr124c, hgap01a, ht23, ht0a, hgap04a, ht4b, hsum0, hgap10b, htr023a, htr014c, hdelta1]
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
                                linarith only [hgap31a, hgap32a, hgap34a, hsum3, hgap30a, hgap33a]
                              ·
                                have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                                linarith only [htr234c, hgap14a, hgap11a, htr124c, ht34, hgap30a, ht01, hgap13a, hgap10b, ht4b, ht0a, hdelta1, hsum1, hgap34b, hgap12a, hgap31a, hgap32a, hgap33a, hsum3, htr014a]
                            ·
                              have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                              linarith only [hc34b, hsum1, hdelta1, hgap10b, hgap11a, hgap33a, hgap33b, hgap12a, htr013a, hgap14a, hgap13a, ht01, ht4b, ht0a]
                          ·
                            have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                            linarith only [hgap11b, hgap32a, htr013b, hgap32b]
                        ·
                          have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
                          rcases hbridge32 with ⟨hzero32, hgap32b⟩ | ⟨hpositive32, hgap32b, hgap32c⟩
                          ·
                            have hgap32a : (s32 : ℝ) = 0 := by exact_mod_cast hzero32
                            rcases hbridge33 with ⟨hzero33, hgap33b⟩ | ⟨hpositive33, hgap33b, hgap33c⟩
                            ·
                              have hgap33a : (s33 : ℝ) = 0 := by exact_mod_cast hzero33
                              rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                              ·
                                have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
                                linarith only [ht4b, htr023c, ht0a, hdelta1, hgap03a, htr234c, hgap31b, hgap33a, ht12, hc23a, hgap34a, hgap30a, hsum3, hgap03b, ht01, htr124c, hc34b, hgap32a, htr014c]
                              ·
                                have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                                linarith only [hgap34a, hgap13a, hgap14a, ht34, ht0a, hsum1, htr013a, ht01, hgap10b, hdelta1, htr123c, htr234c, hgap34b, hgap11a, ht4b, hgap12a, htr124a]
                            ·
                              have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                              linarith only [hgap10b, hsum1, hdelta1, hgap11a, htr013a, hgap14a, hgap33a, ht4b, hgap33b, ht01, hgap13a, hgap12a, hc34b, ht0a]
                          ·
                            have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                            linarith only [hgap32b, hgap32a, htr013b, hgap11b]
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
                                linarith only [hgap34a, htr014c, hsum3, htr124c, hdelta1, htr023a, ht01, hc34b, hgap03b, ht12, hgap03a, hgap32a, hgap33a, ht0a, hgap30b, ht23, ht4b, hgap31a, htr234c]
                              ·
                                have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                                linarith only [htr024a, hgap34b, hgap30b, htr234c, htr023a, hgap34a, hdelta1, hgap30a]
                            ·
                              have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                              linarith only [htr013a, hgap33a, hgap11a, ht0a, hgap33b, hgap13a, hgap14a, ht01, hc34b, hgap10b, hdelta1, ht4b, hgap12a, hsum1]
                          ·
                            have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                            linarith only [hgap32a, htr013b, hgap32b, hgap11b]
                        ·
                          have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
                          linarith only [htr234c, hgap30b, hdelta1, ht0a, hgap03b, hgap31b, hgap03a, ht12, ht23, htr014c, hgap30a, htr124c, ht4b, htr023c, ht01, hgap31a, hc34b]
                    ·
                      have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                      linarith only [hgap03a, hgap14a, htr014c, hdelta1, hgap14b, hgap03b, htr013b, htr023c, hgap10b, hgap10a]
                  ·
                    have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
                    rcases hbridge14 with ⟨hzero14, hgap14b⟩ | ⟨hpositive14, hgap14b, hgap14c⟩
                    ·
                      have hgap14a : (s14 : ℝ) = 0 := by exact_mod_cast hzero14
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
                              linarith only [hgap13a, hgap13b, hgap33b, htr123c, htr124c, htr234c]
                            ·
                              have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                              rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                              ·
                                have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
                                linarith only [hdelta1, hc34b, hgap10a, hgap33b, hgap32a, hgap34a, hgap30a, ht01, ht4b, htr013a, hgap10b, hgap31a, ht0a, hsum3]
                              ·
                                have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                                linarith only [hdelta1, hsum0, hgap02a, hgap00b, htr023c, hgap03b, hgap34b, htr234c, hgap34a, hgap01a, ht0a, ht4b, htr014c, htr013b, ht34, htr124c, hgap04a]
                          ·
                            have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                            linarith only [htr013b, hgap32a, hgap32b, hgap11b]
                        ·
                          have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
                          rcases hbridge32 with ⟨hzero32, hgap32b⟩ | ⟨hpositive32, hgap32b, hgap32c⟩
                          ·
                            have hgap32a : (s32 : ℝ) = 0 := by exact_mod_cast hzero32
                            rcases hbridge33 with ⟨hzero33, hgap33b⟩ | ⟨hpositive33, hgap33b, hgap33c⟩
                            ·
                              have hgap33a : (s33 : ℝ) = 0 := by exact_mod_cast hzero33
                              linarith only [hgap13a, hgap33b, htr123c, htr124c, hgap13b, htr234c]
                            ·
                              have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                              rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                              ·
                                have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
                                rcases hbridge40 with ⟨hzero40, hgap40b⟩ | ⟨hpositive40, hgap40b, hgap40c⟩
                                ·
                                  have hgap40a : (s40 : ℝ) = 0 := by exact_mod_cast hzero40
                                  linarith only [hgap40b, hgap04b, ht0a, ht4b]
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
                                          by_cases hcut00_1nat : s00 ≤ 1
                                          ·
                                            have hcut00_1 : (s00 : ℝ) ≤ 1 := by exact_mod_cast hcut00_1nat
                                            linarith only [ht4b, hgap02a, hsum0, hgap31a, htr014c, hc34b, hgap01a, ht0a, ht01, hgap03b, htr023c, hgap31b, hdelta1, hc23a, ht12, hcut00_1, htr124c, htr234c, hgap04a]
                                          ·
                                            have hcut00_1natpos : 2 ≤ s00 := by omega
                                            have hcut00_1 : (2 : ℝ) ≤ s00 := by exact_mod_cast hcut00_1natpos
                                            linarith only [hdelta1, htr234c, hc34b, htr124c, htr123c, htr013a, hcut00_1, ht4b, hgap13b, hgap13a, ht0a, hgap00b]
                                        ·
                                          have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                                          linarith only [hgap31b, hscore42a, htr023c, hgap03a, ht4b, hgap31a, hsum4, hgap03b, hdelta1, ht12, hscore41a, hscore43a, ht01, hgap44a, ht0a, hgap40c, hc23a]
                                      ·
                                        have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                                        linarith only [hscore41a, hscore42a, ht4b, hsum4, hgap03a, ht12, hgap43a, ht0a, hscore44a, hgap31b, hdelta1, hgap40c, ht01, hc23a, hgap03b, hgap31a, htr023c]
                                    ·
                                      have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                                      linarith only [htr023c, hscore44a, hgap42a, ht4b, hc23a, hscore43a, hdelta1, hscore41a, hgap03b, hgap03a, hgap31a, ht0a, hgap31b, hsum4, ht12, hgap40c, ht01]
                                  ·
                                    have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                                    linarith only [hc23a, ht0a, hgap03b, ht12, hscore42a, hgap31a, hgap03a, hgap40c, htr023c, ht01, hgap41a, hdelta1, hscore43a, hscore44a, hgap31b, hsum4, ht4b]
                              ·
                                have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                                linarith only [hgap33a, hgap34a, hscore30a, hscore32a, hsum3, hgap31a]
                          ·
                            have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                            linarith only [hgap13b, hgap32b, ht12, hc23a, htr234c, hgap31a, ht01, hgap31b, ht4b, ht0a, htr123c, hdelta1, hgap13a, hc34b, htr124c, hgap32a]
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
                              linarith only [hgap13a, hgap13b, htr124c, htr234c, htr123c, hgap33b]
                            ·
                              have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                              rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                              ·
                                have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
                                rcases hbridge40 with ⟨hzero40, hgap40b⟩ | ⟨hpositive40, hgap40b, hgap40c⟩
                                ·
                                  have hgap40a : (s40 : ℝ) = 0 := by exact_mod_cast hzero40
                                  linarith only [hgap04b, ht0a, hgap40b, ht4b]
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
                                          by_cases hcut00_1nat : s00 ≤ 1
                                          ·
                                            have hcut00_1 : (s00 : ℝ) ≤ 1 := by exact_mod_cast hcut00_1nat
                                            linarith only [ht23, ht0a, hgap30a, hgap04a, hgap30b, htr234c, ht01, hsum0, hcut00_1, htr124c, hc34b, hgap01a, ht12, htr014c, hgap03b, htr023a, ht4b, hgap02a, hdelta1]
                                          ·
                                            have hcut00_1natpos : 2 ≤ s00 := by omega
                                            have hcut00_1 : (2 : ℝ) ≤ s00 := by exact_mod_cast hcut00_1natpos
                                            linarith only [hgap13b, hdelta1, ht0a, htr123c, hgap00b, hgap13a, htr234c, hcut00_1, hc34b, ht4b, htr013a, htr124c]
                                        ·
                                          have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                                          linarith only [hscore43a, hsum4, ht0a, ht01, hscore42a, hscore41a, hgap30a, ht23, hgap03b, hgap30b, htr023a, ht4b, hgap03a, hdelta1, hgap44a, hgap40c, ht12]
                                      ·
                                        have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                                        linarith only [hgap03a, hscore42a, hgap40c, hscore44a, hgap03b, htr023a, hscore41a, ht0a, hsum4, ht23, hgap30b, hdelta1, hgap43a, hgap30a, ht4b, ht12, ht01]
                                    ·
                                      have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                                      linarith only [ht0a, ht01, hgap03a, hgap03b, hgap30a, hsum4, hdelta1, hgap30b, hgap42a, ht23, hscore43a, ht4b, hgap40c, hscore41a, hscore44a, htr023a, ht12]
                                  ·
                                    have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                                    linarith only [hgap41a, ht12, ht23, hscore44a, hgap30b, hgap40c, hgap30a, ht01, hgap03b, hdelta1, hscore42a, htr023a, ht0a, hgap03a, ht4b, hscore43a, hsum4]
                              ·
                                have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                                linarith only [hsum3, hgap34a, hgap30a, hgap33a, hscore31a, hscore32a]
                          ·
                            have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                            linarith only [hgap11b, hgap32a, htr013b, hgap32b]
                        ·
                          have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
                          linarith only [hc34b, htr124c, hgap31a, hdelta1, hgap30b, htr012c, hgap31b, hgap13a, ht23, ht0a, hgap13b, htr023c, ht4b, ht01, ht12, htr234c, hgap30a]
                    ·
                      have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                      linarith only [hgap13a, hgap14a, hgap10a, hscore12a, hsum1, hscore11a]
                ·
                  have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
                  linarith only [hgap10b, ht4b, htr124a, hgap12b, hgap10a, ht01, hgap12a, htr234c, hc34b, hdelta1, ht0a, htr013a]
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
                                linarith only [hgap33a, hgap30a, hsum3, hgap32a, hgap34a, hgap31a]
                              ·
                                have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                                linarith only [htr234c, ht34, ht4b, htr123c, hgap34b, hgap31a, hgap10a, hgap10b, hgap30a, hgap32a, hgap33a, hgap11b, htr124a, ht01, hgap11a, hsum3, ht0a, hdelta1]
                            ·
                              have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                              linarith only [ht0a, hdelta1, ht4b, hgap33b, hgap11b, hgap10a, hgap11a, hc34b, ht01, hgap10b, hgap33a]
                          ·
                            have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                            rcases hbridge33 with ⟨hzero33, hgap33b⟩ | ⟨hpositive33, hgap33b, hgap33c⟩
                            ·
                              have hgap33a : (s33 : ℝ) = 0 := by exact_mod_cast hzero33
                              rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                              ·
                                have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
                                linarith only [ht01, hgap31a, hgap34a, hgap33a, htr013b, ht4b, hsum3, hgap10b, hgap32b, hdelta1, htr234c, ht0a, hgap10a, htr124a, hc34b, htr123c, hgap30a]
                              ·
                                have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                                linarith only [ht4b, hdelta1, hgap34a, hgap32a, htr123c, ht01, hgap32b, ht0a, ht34, hgap10a, htr013b, htr124a, hgap10b, hgap34b, htr234c]
                            ·
                              have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                              linarith only [hgap10b, ht0a, hc34b, hgap33a, hgap33b, hgap32a, hdelta1, htr013b, hgap32b, ht4b, hgap10a, ht01]
                        ·
                          have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
                          rcases hbridge32 with ⟨hzero32, hgap32b⟩ | ⟨hpositive32, hgap32b, hgap32c⟩
                          ·
                            have hgap32a : (s32 : ℝ) = 0 := by exact_mod_cast hzero32
                            rcases hbridge33 with ⟨hzero33, hgap33b⟩ | ⟨hpositive33, hgap33b, hgap33c⟩
                            ·
                              have hgap33a : (s33 : ℝ) = 0 := by exact_mod_cast hzero33
                              rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                              ·
                                have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
                                linarith only [hc34b, hgap32a, ht0a, hgap31b, hgap30a, htr014c, hsum3, ht01, hc23a, hdelta1, ht12, htr234c, htr124c, hgap03a, htr023c, hgap33a, ht4b, hgap03b, hgap34a]
                              ·
                                have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                                linarith only [htr234c, hdelta1, htr014c, ht12, ht4b, hgap03a, hgap03b, ht01, htr124c, hgap31a, ht0a, hgap34a, htr023c, ht34, hgap31b, hc23a, hgap34b]
                            ·
                              have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                              linarith only [htr234c, hgap31a, hsum0, ht0a, hgap04a, htr124c, hgap02a, hc23a, hgap11b, hgap03b, ht12, hdelta1, hgap31b, htr014c, ht01, hgap33a, ht4b, hgap00b, htr023c, hgap01a, hgap11a, hgap33b, hc34b]
                          ·
                            have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                            linarith only [ht4b, ht12, htr124a, hdelta1, ht0a, hgap31a, htr123c, hc34b, ht01, hgap32a, hgap32b, hgap31b, hc23a, htr234c]
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
                                linarith only [htr124c, ht0a, hgap33a, hgap31a, hc34b, ht12, ht01, hgap03b, hdelta1, hgap30b, ht23, htr234c, hgap32a, htr023a, hsum3, htr014c, hgap34a, ht4b, hgap03a]
                              ·
                                have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                                linarith only [hdelta1, hgap30a, hgap34a, htr023a, hgap34b, hgap30b, htr234c, htr124a, htr012c]
                            ·
                              have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                              linarith only [htr014c, htr023a, ht0a, ht01, hgap04a, hsum0, hgap02a, hgap03b, htr234c, hgap00b, hgap30b, hgap11b, hgap33a, hgap33b, hdelta1, ht4b, hc34b, hgap11a, hgap30a, hgap01a, htr124c, ht23, ht12]
                          ·
                            have hgap32a : (1 : ℝ) ≤ s32 := by exact_mod_cast hpositive32
                            rcases hbridge33 with ⟨hzero33, hgap33b⟩ | ⟨hpositive33, hgap33b, hgap33c⟩
                            ·
                              have hgap33a : (s33 : ℝ) = 0 := by exact_mod_cast hzero33
                              rcases hbridge34 with ⟨hzero34, hgap34b⟩ | ⟨hpositive34, hgap34b, hgap34c⟩
                              ·
                                have hgap34a : (s34 : ℝ) = 0 := by exact_mod_cast hzero34
                                rcases hbridge40 with ⟨hzero40, hgap40b⟩ | ⟨hpositive40, hgap40b, hgap40c⟩
                                ·
                                  have hgap40a : (s40 : ℝ) = 0 := by exact_mod_cast hzero40
                                  linarith only [hgap04b, hgap40b, ht4b, ht0a]
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
                                          by_cases hcut00_1nat : s00 ≤ 1
                                          ·
                                            have hcut00_1 : (s00 : ℝ) ≤ 1 := by exact_mod_cast hcut00_1nat
                                            linarith only [hc34b, ht23, hgap02a, hsum0, htr014c, hgap30a, hgap30b, ht4b, hgap03b, hdelta1, htr234c, htr023a, hgap04a, htr124c, hcut00_1, hgap01a, ht2a]
                                          ·
                                            have hcut00_1natpos : 2 ≤ s00 := by omega
                                            have hcut00_1 : (2 : ℝ) ≤ s00 := by exact_mod_cast hcut00_1natpos
                                            linarith only [hc34b, htr234c, hgap11a, ht4b, hcut00_1, htr124a, hdelta1, hgap11b, ht0a, htr123c, hgap00b]
                                        ·
                                          have hgap44a : (1 : ℝ) ≤ s44 := by exact_mod_cast hpositive44
                                          linarith only [hdelta1, ht0a, ht23, hgap44a, hgap30a, hgap03a, hgap30b, hscore43a, hscore41a, hgap03b, hsum4, hgap40c, ht01, ht4b, hscore42a, htr023a, ht12]
                                      ·
                                        have hgap43a : (1 : ℝ) ≤ s43 := by exact_mod_cast hpositive43
                                        linarith only [hgap03b, hscore44a, hscore42a, hsum4, ht4b, hscore41a, hgap30a, ht12, hgap30b, ht23, hgap43a, hgap03a, hgap40c, ht0a, ht01, hdelta1, htr023a]
                                    ·
                                      have hgap42a : (1 : ℝ) ≤ s42 := by exact_mod_cast hpositive42
                                      linarith only [hdelta1, ht0a, hscore44a, ht01, hgap03a, hgap42a, ht4b, hgap30b, ht23, hsum4, hscore41a, htr023a, ht12, hgap30a, hgap40c, hscore43a, hgap03b]
                                  ·
                                    have hgap41a : (1 : ℝ) ≤ s41 := by exact_mod_cast hpositive41
                                    linarith only [hscore44a, hgap30b, hgap30a, hsum4, hscore42a, ht23, hgap40c, hscore43a, hdelta1, hgap41a, ht01, hgap03b, ht12, htr023a, ht0a, ht4b, hgap03a]
                              ·
                                have hgap34a : (1 : ℝ) ≤ s34 := by exact_mod_cast hpositive34
                                linarith only [hscore33a, hscore31a, hgap34a, hsum3, hgap30a, hgap32a]
                            ·
                              have hgap33a : (1 : ℝ) ≤ s33 := by exact_mod_cast hpositive33
                              linarith only [hsum3, hscore34a, hgap32a, hgap33a, hgap30a, hscore31a]
                        ·
                          have hgap31a : (1 : ℝ) ≤ s31 := by exact_mod_cast hpositive31
                          linarith only [hgap31b, hgap03b, htr023c, hgap31a, hgap11b, ht0a, hgap30a, hgap30b, hgap11a, hsum0, htr234c, hgap00b, ht23, hc12b, ht4b, hgap02a, hgap01a, hdelta1, htr124c, htr014c, htr123c, hc34b, hgap04a]
                    ·
                      have hgap14a : (1 : ℝ) ≤ s14 := by exact_mod_cast hpositive14
                      linarith only [hscore12a, hgap11a, hscore13a, hgap10a, hsum1, hgap14a]
                  ·
                    have hgap13a : (1 : ℝ) ≤ s13 := by exact_mod_cast hpositive13
                    linarith only [hgap13a, hscore14a, hsum1, hscore12a, hgap10a, hgap11a]
                ·
                  have hgap12a : (1 : ℝ) ≤ s12 := by exact_mod_cast hpositive12
                  linarith only [hgap11a, hgap10a, hsum1, hgap12a, hscore13a, hscore14a]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            linarith only [hgap03a, hdelta1, hgap04a, htr023a, ht01, hgap03b, hc23a, ht12, hgap04b]
      ·
        have hgap02a : (1 : ℝ) ≤ s02 := by exact_mod_cast hpositive02
        rcases hbridge03 with ⟨hzero03, hgap03b⟩ | ⟨hpositive03, hgap03b, hgap03c⟩
        ·
          have hgap03a : (s03 : ℝ) = 0 := by exact_mod_cast hzero03
          rcases hbridge04 with ⟨hzero04, hgap04b⟩ | ⟨hpositive04, hgap04b, hgap04c⟩
          ·
            have hgap04a : (s04 : ℝ) = 0 := by exact_mod_cast hzero04
            linarith only [hc24b, ht0a, htr013b, hsum0, hgap02b, hgap01a, hgap03a, hgap04a, hdelta1, htr124a, htr012c, ht4b, hgap00b]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            linarith only [hgap02a, hgap04a, hdelta1, htr024b, hgap00b, hgap02b, hgap04b, hgap00a, htr013b]
        ·
          have hgap03a : (1 : ℝ) ≤ s03 := by exact_mod_cast hpositive03
          linarith only [hgap03a, hc04b, hgap00b, ht0a, hgap02a, htr013b, hgap03b, hdelta1, ht4b, hgap02b, hgap00a]
    ·
      have hgap01a : (1 : ℝ) ≤ s01 := by exact_mod_cast hpositive01
      rcases hbridge02 with ⟨hzero02, hgap02b⟩ | ⟨hpositive02, hgap02b, hgap02c⟩
      ·
        have hgap02a : (s02 : ℝ) = 0 := by exact_mod_cast hzero02
        rcases hbridge03 with ⟨hzero03, hgap03b⟩ | ⟨hpositive03, hgap03b, hgap03c⟩
        ·
          have hgap03a : (s03 : ℝ) = 0 := by exact_mod_cast hzero03
          rcases hbridge04 with ⟨hzero04, hgap04b⟩ | ⟨hpositive04, hgap04b, hgap04c⟩
          ·
            have hgap04a : (s04 : ℝ) = 0 := by exact_mod_cast hzero04
            linarith only [ht0a, hgap01b, htr124a, hgap00b, ht4b, hgap04a, hc24b, hdelta1, htr013c, hsum0, hgap02a, htr123c, hgap03a]
          ·
            have hgap04a : (1 : ℝ) ≤ s04 := by exact_mod_cast hpositive04
            linarith only [hdelta1, hgap00a, hgap01b, hgap01a, hgap04b, hgap00b, htr024b, hgap04a, htr023c]
        ·
          have hgap03a : (1 : ℝ) ≤ s03 := by exact_mod_cast hpositive03
          linarith only [hgap00b, hdelta1, hgap00a, hgap01b, hgap03b, ht0a, hgap01a, ht4b, hc04b, htr023c, hgap03a]
      ·
        have hgap02a : (1 : ℝ) ≤ s02 := by exact_mod_cast hpositive02
        linarith only [ht2b, hgap00a, hgap02b, hgap00b, hgap02a, hdelta1, hgap01b, ht0a, hgap01a, hc02b]

#print axioms n5_between_mask072
end Jsp404.SixExactFloorKernel
