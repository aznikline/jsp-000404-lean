import Jsp000404.SixExactFloorKernelSymbolicInterval
import Jsp000404.SixExactFloorKernelSymbolicMask127Integer

/-! Unbounded-n fixed-orientation prototype. Every integer cut is derived
from actual ModelSix gap facts before the ordinary omega closure. -/
namespace Jsp404.SixExactFloorKernel

set_option maxHeartbeats 16000000 in
theorem symbolic_mask127_probe {n : ℕ} (M : SixModelCompression.ModelSix n)
    (hn4 : 4 ≤ n) (hhigh : (1/2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    (htri012 : M.d 1 2+1 ≤ M.d 0 1 ∧ M.d 1 2 < M.d 0 2 ∧ M.d 0 2 < M.d 0 1)
    (htri013 : M.d 1 3+1 ≤ M.d 0 1 ∧ M.d 1 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 1)
    (htri014 : M.d 1 4+1 ≤ M.d 0 1 ∧ M.d 1 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 1)
    (htri023 : M.d 2 3+1 ≤ M.d 0 2 ∧ M.d 2 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 2)
    (htri024 : M.d 2 4+1 ≤ M.d 0 2 ∧ M.d 2 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 2)
    (htri034 : M.d 3 4+1 ≤ M.d 0 3 ∧ M.d 3 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 3)
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
  obtain ⟨hc02a, hc02b⟩ := M.corridor 0 2 (by decide)
  obtain ⟨hc03a, hc03b⟩ := M.corridor 0 3 (by decide)
  obtain ⟨hc04a, hc04b⟩ := M.corridor 0 4 (by decide)
  obtain ⟨hc12a, hc12b⟩ := M.corridor 1 2 (by decide)
  obtain ⟨hc13a, hc13b⟩ := M.corridor 1 3 (by decide)
  obtain ⟨hc14a, hc14b⟩ := M.corridor 1 4 (by decide)
  obtain ⟨hc23a, hc23b⟩ := M.corridor 2 3 (by decide)
  obtain ⟨hc24a, hc24b⟩ := M.corridor 2 4 (by decide)
  obtain ⟨hc34a, hc34b⟩ := M.corridor 3 4 (by decide)
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
  have hsort0 : ([M.d 0 4, M.d 0 3, M.d 0 2, M.d 0 1] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp0 := M.row_perm 0
  have he0 : (((List.finRange 5).erase (0 : Fin 5)).map (M.d 0)) = [M.d 0 1, M.d 0 2, M.d 0 3, M.d 0 4] := by
    norm_num [List.finRange, List.ofFn_succ]
  rw [he0] at hp0
  have hperm0 := hp0.trans (((((((((List.Perm.swap (M.d 0 4) (M.d 0 3) []).cons (M.d 0 2)).cons (M.d 0 1)).trans ((List.Perm.swap (M.d 0 4) (M.d 0 2) [M.d 0 3]).cons (M.d 0 1))).trans (List.Perm.swap (M.d 0 4) (M.d 0 1) [M.d 0 2, M.d 0 3])).trans (((List.Perm.swap (M.d 0 3) (M.d 0 2) []).cons (M.d 0 1)).cons (M.d 0 4))).trans ((List.Perm.swap (M.d 0 3) (M.d 0 1) [M.d 0 2]).cons (M.d 0 4))).trans (((List.Perm.swap (M.d 0 2) (M.d 0 1) []).cons (M.d 0 3)).cons (M.d 0 4))))
  have hrow0 : M.rowxs 0 = [M.d 0 4, M.d 0 3, M.d 0 2, M.d 0 1] := hperm0.eq_of_pairwise' (M.row_sorted 0) hsort0
  have hrow_nonneg0 := SmallScoreGapBounds.model_gaps_nonneg M 0
  simp only [SmallScoreGapBounds.modelGaps, hrow0, StrongGapBudget.linearGaps] at hrow_nonneg0
  let s00 : ℕ := ⌊(M.d 0 4 - M.theta 0)⌋₊ - 1
  let u00 : ℕ := min s00 1
  have hnonneg00 : 0 ≤ (M.d 0 4 - M.theta 0) := hrow_nonneg0 (M.d 0 4 - M.theta 0) (by simp)
  obtain ⟨hgap00b, hgap00c⟩ := score_gap_min_interval (M.d 0 4 - M.theta 0) hnonneg00
  change (s00 : ℝ) + (u00 : ℝ) ≤ (M.d 0 4 - M.theta 0) at hgap00b
  change (M.d 0 4 - M.theta 0) < (s00 : ℝ) + 2 at hgap00c
  let s01 : ℕ := ⌊(M.d 0 3 - M.d 0 4)⌋₊ - 1
  let u01 : ℕ := min s01 1
  have hnonneg01 : 0 ≤ (M.d 0 3 - M.d 0 4) := hrow_nonneg0 (M.d 0 3 - M.d 0 4) (by simp)
  obtain ⟨hgap01b, hgap01c⟩ := score_gap_min_interval (M.d 0 3 - M.d 0 4) hnonneg01
  change (s01 : ℝ) + (u01 : ℝ) ≤ (M.d 0 3 - M.d 0 4) at hgap01b
  change (M.d 0 3 - M.d 0 4) < (s01 : ℝ) + 2 at hgap01c
  let s02 : ℕ := ⌊(M.d 0 2 - M.d 0 3)⌋₊ - 1
  let u02 : ℕ := min s02 1
  have hnonneg02 : 0 ≤ (M.d 0 2 - M.d 0 3) := hrow_nonneg0 (M.d 0 2 - M.d 0 3) (by simp)
  obtain ⟨hgap02b, hgap02c⟩ := score_gap_min_interval (M.d 0 2 - M.d 0 3) hnonneg02
  change (s02 : ℝ) + (u02 : ℝ) ≤ (M.d 0 2 - M.d 0 3) at hgap02b
  change (M.d 0 2 - M.d 0 3) < (s02 : ℝ) + 2 at hgap02c
  let s03 : ℕ := ⌊(M.d 0 1 - M.d 0 2)⌋₊ - 1
  let u03 : ℕ := min s03 1
  have hnonneg03 : 0 ≤ (M.d 0 1 - M.d 0 2) := hrow_nonneg0 (M.d 0 1 - M.d 0 2) (by simp)
  obtain ⟨hgap03b, hgap03c⟩ := score_gap_min_interval (M.d 0 1 - M.d 0 2) hnonneg03
  change (s03 : ℝ) + (u03 : ℝ) ≤ (M.d 0 1 - M.d 0 2) at hgap03b
  change (M.d 0 1 - M.d 0 2) < (s03 : ℝ) + 2 at hgap03c
  let s04 : ℕ := ⌊(M.theta 0 + ((n : ℝ) + M.delta) - M.d 0 1)⌋₊ - 1
  let u04 : ℕ := min s04 1
  have hnonneg04 : 0 ≤ (M.theta 0 + ((n : ℝ) + M.delta) - M.d 0 1) := hrow_nonneg0 (M.theta 0 + ((n : ℝ) + M.delta) - M.d 0 1) (by simp)
  obtain ⟨hgap04b, hgap04c⟩ := score_gap_min_interval (M.theta 0 + ((n : ℝ) + M.delta) - M.d 0 1) hnonneg04
  change (s04 : ℝ) + (u04 : ℝ) ≤ (M.theta 0 + ((n : ℝ) + M.delta) - M.d 0 1) at hgap04b
  change (M.theta 0 + ((n : ℝ) + M.delta) - M.d 0 1) < (s04 : ℝ) + 2 at hgap04c
  have hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n := by
    have h := SmallScoreGapBounds.model_score M 0 2 hdef0
    simp only [SmallScoreGapBounds.modelGaps, hrow0, StrongGapBudget.linearGaps, StrongGapBudget.score, List.map_cons, List.sum_cons, List.sum_nil] at h
    change (s00 + (s01 + (s02 + (s03 + (s04 + 0))))) + 2 = n at h
    omega
  have hsort1 : ([M.d 1 3, M.d 1 2, M.d 1 4, M.d 0 1] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hp1 := M.row_perm 1
  have hcanon10 : M.d 1 0 = M.d 0 1 := M.symm 1 0 (by decide)
  have he1 : (((List.finRange 5).erase (1 : Fin 5)).map (M.d 1)) = [M.d 0 1, M.d 1 2, M.d 1 3, M.d 1 4] := by
    norm_num [List.finRange, List.ofFn_succ, hcanon10]
  rw [he1] at hp1
  have hperm1 := hp1.trans ((((((List.Perm.swap (M.d 1 3) (M.d 1 2) [M.d 1 4]).cons (M.d 0 1)).trans (List.Perm.swap (M.d 1 3) (M.d 0 1) [M.d 1 2, M.d 1 4])).trans ((List.Perm.swap (M.d 1 2) (M.d 0 1) [M.d 1 4]).cons (M.d 1 3))).trans (((List.Perm.swap (M.d 1 4) (M.d 0 1) []).cons (M.d 1 2)).cons (M.d 1 3))))
  have hrow1 : M.rowxs 1 = [M.d 1 3, M.d 1 2, M.d 1 4, M.d 0 1] := hperm1.eq_of_pairwise' (M.row_sorted 1) hsort1
  have hrow_nonneg1 := SmallScoreGapBounds.model_gaps_nonneg M 1
  simp only [SmallScoreGapBounds.modelGaps, hrow1, StrongGapBudget.linearGaps] at hrow_nonneg1
  let s10 : ℕ := ⌊(M.d 1 3 - M.theta 1)⌋₊ - 1
  let u10 : ℕ := min s10 1
  have hnonneg10 : 0 ≤ (M.d 1 3 - M.theta 1) := hrow_nonneg1 (M.d 1 3 - M.theta 1) (by simp)
  obtain ⟨hgap10b, hgap10c⟩ := score_gap_min_interval (M.d 1 3 - M.theta 1) hnonneg10
  change (s10 : ℝ) + (u10 : ℝ) ≤ (M.d 1 3 - M.theta 1) at hgap10b
  change (M.d 1 3 - M.theta 1) < (s10 : ℝ) + 2 at hgap10c
  let s11 : ℕ := ⌊(M.d 1 2 - M.d 1 3)⌋₊ - 1
  let u11 : ℕ := min s11 1
  have hnonneg11 : 0 ≤ (M.d 1 2 - M.d 1 3) := hrow_nonneg1 (M.d 1 2 - M.d 1 3) (by simp)
  obtain ⟨hgap11b, hgap11c⟩ := score_gap_min_interval (M.d 1 2 - M.d 1 3) hnonneg11
  change (s11 : ℝ) + (u11 : ℝ) ≤ (M.d 1 2 - M.d 1 3) at hgap11b
  change (M.d 1 2 - M.d 1 3) < (s11 : ℝ) + 2 at hgap11c
  let s12 : ℕ := ⌊(M.d 1 4 - M.d 1 2)⌋₊ - 1
  let u12 : ℕ := min s12 1
  have hnonneg12 : 0 ≤ (M.d 1 4 - M.d 1 2) := hrow_nonneg1 (M.d 1 4 - M.d 1 2) (by simp)
  obtain ⟨hgap12b, hgap12c⟩ := score_gap_min_interval (M.d 1 4 - M.d 1 2) hnonneg12
  change (s12 : ℝ) + (u12 : ℝ) ≤ (M.d 1 4 - M.d 1 2) at hgap12b
  change (M.d 1 4 - M.d 1 2) < (s12 : ℝ) + 2 at hgap12c
  let s13 : ℕ := ⌊(M.d 0 1 - M.d 1 4)⌋₊ - 1
  let u13 : ℕ := min s13 1
  have hnonneg13 : 0 ≤ (M.d 0 1 - M.d 1 4) := hrow_nonneg1 (M.d 0 1 - M.d 1 4) (by simp)
  obtain ⟨hgap13b, hgap13c⟩ := score_gap_min_interval (M.d 0 1 - M.d 1 4) hnonneg13
  change (s13 : ℝ) + (u13 : ℝ) ≤ (M.d 0 1 - M.d 1 4) at hgap13b
  change (M.d 0 1 - M.d 1 4) < (s13 : ℝ) + 2 at hgap13c
  let s14 : ℕ := ⌊(M.theta 1 + ((n : ℝ) + M.delta) - M.d 0 1)⌋₊ - 1
  let u14 : ℕ := min s14 1
  have hnonneg14 : 0 ≤ (M.theta 1 + ((n : ℝ) + M.delta) - M.d 0 1) := hrow_nonneg1 (M.theta 1 + ((n : ℝ) + M.delta) - M.d 0 1) (by simp)
  obtain ⟨hgap14b, hgap14c⟩ := score_gap_min_interval (M.theta 1 + ((n : ℝ) + M.delta) - M.d 0 1) hnonneg14
  change (s14 : ℝ) + (u14 : ℝ) ≤ (M.theta 1 + ((n : ℝ) + M.delta) - M.d 0 1) at hgap14b
  change (M.theta 1 + ((n : ℝ) + M.delta) - M.d 0 1) < (s14 : ℝ) + 2 at hgap14c
  have hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n := by
    have h := SmallScoreGapBounds.model_score M 1 3 hdef1
    simp only [SmallScoreGapBounds.modelGaps, hrow1, StrongGapBudget.linearGaps, StrongGapBudget.score, List.map_cons, List.sum_cons, List.sum_nil] at h
    change (s10 + (s11 + (s12 + (s13 + (s14 + 0))))) + 3 = n at h
    omega
  have hsort3 : ([M.d 2 3, M.d 1 3, M.d 3 4, M.d 0 3] : List ℝ).Pairwise (· ≤ ·) := by
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
  have hperm3 := hp3.trans ((((((List.Perm.swap (M.d 2 3) (M.d 1 3) [M.d 3 4]).cons (M.d 0 3)).trans (List.Perm.swap (M.d 2 3) (M.d 0 3) [M.d 1 3, M.d 3 4])).trans ((List.Perm.swap (M.d 1 3) (M.d 0 3) [M.d 3 4]).cons (M.d 2 3))).trans (((List.Perm.swap (M.d 3 4) (M.d 0 3) []).cons (M.d 1 3)).cons (M.d 2 3))))
  have hrow3 : M.rowxs 3 = [M.d 2 3, M.d 1 3, M.d 3 4, M.d 0 3] := hperm3.eq_of_pairwise' (M.row_sorted 3) hsort3
  have hrow_nonneg3 := SmallScoreGapBounds.model_gaps_nonneg M 3
  simp only [SmallScoreGapBounds.modelGaps, hrow3, StrongGapBudget.linearGaps] at hrow_nonneg3
  let s30 : ℕ := ⌊(M.d 2 3 - M.theta 3)⌋₊ - 1
  let u30 : ℕ := min s30 1
  have hnonneg30 : 0 ≤ (M.d 2 3 - M.theta 3) := hrow_nonneg3 (M.d 2 3 - M.theta 3) (by simp)
  obtain ⟨hgap30b, hgap30c⟩ := score_gap_min_interval (M.d 2 3 - M.theta 3) hnonneg30
  change (s30 : ℝ) + (u30 : ℝ) ≤ (M.d 2 3 - M.theta 3) at hgap30b
  change (M.d 2 3 - M.theta 3) < (s30 : ℝ) + 2 at hgap30c
  let s31 : ℕ := ⌊(M.d 1 3 - M.d 2 3)⌋₊ - 1
  let u31 : ℕ := min s31 1
  have hnonneg31 : 0 ≤ (M.d 1 3 - M.d 2 3) := hrow_nonneg3 (M.d 1 3 - M.d 2 3) (by simp)
  obtain ⟨hgap31b, hgap31c⟩ := score_gap_min_interval (M.d 1 3 - M.d 2 3) hnonneg31
  change (s31 : ℝ) + (u31 : ℝ) ≤ (M.d 1 3 - M.d 2 3) at hgap31b
  change (M.d 1 3 - M.d 2 3) < (s31 : ℝ) + 2 at hgap31c
  let s32 : ℕ := ⌊(M.d 3 4 - M.d 1 3)⌋₊ - 1
  let u32 : ℕ := min s32 1
  have hnonneg32 : 0 ≤ (M.d 3 4 - M.d 1 3) := hrow_nonneg3 (M.d 3 4 - M.d 1 3) (by simp)
  obtain ⟨hgap32b, hgap32c⟩ := score_gap_min_interval (M.d 3 4 - M.d 1 3) hnonneg32
  change (s32 : ℝ) + (u32 : ℝ) ≤ (M.d 3 4 - M.d 1 3) at hgap32b
  change (M.d 3 4 - M.d 1 3) < (s32 : ℝ) + 2 at hgap32c
  let s33 : ℕ := ⌊(M.d 0 3 - M.d 3 4)⌋₊ - 1
  let u33 : ℕ := min s33 1
  have hnonneg33 : 0 ≤ (M.d 0 3 - M.d 3 4) := hrow_nonneg3 (M.d 0 3 - M.d 3 4) (by simp)
  obtain ⟨hgap33b, hgap33c⟩ := score_gap_min_interval (M.d 0 3 - M.d 3 4) hnonneg33
  change (s33 : ℝ) + (u33 : ℝ) ≤ (M.d 0 3 - M.d 3 4) at hgap33b
  change (M.d 0 3 - M.d 3 4) < (s33 : ℝ) + 2 at hgap33c
  let s34 : ℕ := ⌊(M.theta 3 + ((n : ℝ) + M.delta) - M.d 0 3)⌋₊ - 1
  let u34 : ℕ := min s34 1
  have hnonneg34 : 0 ≤ (M.theta 3 + ((n : ℝ) + M.delta) - M.d 0 3) := hrow_nonneg3 (M.theta 3 + ((n : ℝ) + M.delta) - M.d 0 3) (by simp)
  obtain ⟨hgap34b, hgap34c⟩ := score_gap_min_interval (M.theta 3 + ((n : ℝ) + M.delta) - M.d 0 3) hnonneg34
  change (s34 : ℝ) + (u34 : ℝ) ≤ (M.theta 3 + ((n : ℝ) + M.delta) - M.d 0 3) at hgap34b
  change (M.theta 3 + ((n : ℝ) + M.delta) - M.d 0 3) < (s34 : ℝ) + 2 at hgap34c
  have hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n := by
    have h := SmallScoreGapBounds.model_score M 3 3 hdef3
    simp only [SmallScoreGapBounds.modelGaps, hrow3, StrongGapBudget.linearGaps, StrongGapBudget.score, List.map_cons, List.sum_cons, List.sum_nil] at h
    change (s30 + (s31 + (s32 + (s33 + (s34 + 0))))) + 3 = n at h
    omega
  have hsort4 : ([M.d 1 4, M.d 2 4, M.d 3 4, M.d 0 4] : List ℝ).Pairwise (· ≤ ·) := by
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
  have hperm4 := hp4.trans ((((List.Perm.swap (M.d 1 4) (M.d 0 4) [M.d 2 4, M.d 3 4]).trans ((List.Perm.swap (M.d 2 4) (M.d 0 4) [M.d 3 4]).cons (M.d 1 4))).trans (((List.Perm.swap (M.d 3 4) (M.d 0 4) []).cons (M.d 2 4)).cons (M.d 1 4))))
  have hrow4 : M.rowxs 4 = [M.d 1 4, M.d 2 4, M.d 3 4, M.d 0 4] := hperm4.eq_of_pairwise' (M.row_sorted 4) hsort4
  have hrow_nonneg4 := SmallScoreGapBounds.model_gaps_nonneg M 4
  simp only [SmallScoreGapBounds.modelGaps, hrow4, StrongGapBudget.linearGaps] at hrow_nonneg4
  let s40 : ℕ := ⌊(M.d 1 4 - M.theta 4)⌋₊ - 1
  let u40 : ℕ := min s40 1
  have hnonneg40 : 0 ≤ (M.d 1 4 - M.theta 4) := hrow_nonneg4 (M.d 1 4 - M.theta 4) (by simp)
  obtain ⟨hgap40b, hgap40c⟩ := score_gap_min_interval (M.d 1 4 - M.theta 4) hnonneg40
  change (s40 : ℝ) + (u40 : ℝ) ≤ (M.d 1 4 - M.theta 4) at hgap40b
  change (M.d 1 4 - M.theta 4) < (s40 : ℝ) + 2 at hgap40c
  let s41 : ℕ := ⌊(M.d 2 4 - M.d 1 4)⌋₊ - 1
  let u41 : ℕ := min s41 1
  have hnonneg41 : 0 ≤ (M.d 2 4 - M.d 1 4) := hrow_nonneg4 (M.d 2 4 - M.d 1 4) (by simp)
  obtain ⟨hgap41b, hgap41c⟩ := score_gap_min_interval (M.d 2 4 - M.d 1 4) hnonneg41
  change (s41 : ℝ) + (u41 : ℝ) ≤ (M.d 2 4 - M.d 1 4) at hgap41b
  change (M.d 2 4 - M.d 1 4) < (s41 : ℝ) + 2 at hgap41c
  let s42 : ℕ := ⌊(M.d 3 4 - M.d 2 4)⌋₊ - 1
  let u42 : ℕ := min s42 1
  have hnonneg42 : 0 ≤ (M.d 3 4 - M.d 2 4) := hrow_nonneg4 (M.d 3 4 - M.d 2 4) (by simp)
  obtain ⟨hgap42b, hgap42c⟩ := score_gap_min_interval (M.d 3 4 - M.d 2 4) hnonneg42
  change (s42 : ℝ) + (u42 : ℝ) ≤ (M.d 3 4 - M.d 2 4) at hgap42b
  change (M.d 3 4 - M.d 2 4) < (s42 : ℝ) + 2 at hgap42c
  let s43 : ℕ := ⌊(M.d 0 4 - M.d 3 4)⌋₊ - 1
  let u43 : ℕ := min s43 1
  have hnonneg43 : 0 ≤ (M.d 0 4 - M.d 3 4) := hrow_nonneg4 (M.d 0 4 - M.d 3 4) (by simp)
  obtain ⟨hgap43b, hgap43c⟩ := score_gap_min_interval (M.d 0 4 - M.d 3 4) hnonneg43
  change (s43 : ℝ) + (u43 : ℝ) ≤ (M.d 0 4 - M.d 3 4) at hgap43b
  change (M.d 0 4 - M.d 3 4) < (s43 : ℝ) + 2 at hgap43c
  let s44 : ℕ := ⌊(M.theta 4 + ((n : ℝ) + M.delta) - M.d 0 4)⌋₊ - 1
  let u44 : ℕ := min s44 1
  have hnonneg44 : 0 ≤ (M.theta 4 + ((n : ℝ) + M.delta) - M.d 0 4) := hrow_nonneg4 (M.theta 4 + ((n : ℝ) + M.delta) - M.d 0 4) (by simp)
  obtain ⟨hgap44b, hgap44c⟩ := score_gap_min_interval (M.theta 4 + ((n : ℝ) + M.delta) - M.d 0 4) hnonneg44
  change (s44 : ℝ) + (u44 : ℝ) ≤ (M.theta 4 + ((n : ℝ) + M.delta) - M.d 0 4) at hgap44b
  change (M.theta 4 + ((n : ℝ) + M.delta) - M.d 0 4) < (s44 : ℝ) + 2 at hgap44c
  have hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n := by
    have h := SmallScoreGapBounds.model_score M 4 2 hdef4
    simp only [SmallScoreGapBounds.modelGaps, hrow4, StrongGapBudget.linearGaps, StrongGapBudget.score, List.map_cons, List.sum_cons, List.sum_nil] at h
    change (s40 + (s41 + (s42 + (s43 + (s44 + 0))))) + 2 = n at h
    omega
  have hcut55 : (s30 + s32 + s33 + u30 + u32 + u33) + 1 ≤ (n) := by
    have hreal : (((s30 + s32 + s33 + u30 + u32 + u33) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [ht23, hc02b, htr023c, hgap30b, hnonneg31, hgap32b, hgap33b, hdelta1]
    have hnat : (s30 + s32 + s33 + u30 + u32 + u33) < (n) := by exact_mod_cast hreal
    omega
  have hcut4 : (s02 + s03 + s10 + s14 + s32 + s33 + u02 + u03 + u10 + u14 + u32 + u33) + 1 ≤ (n + 1) := by
    have hreal : (((s02 + s03 + s10 + s14 + s32 + s33 + u02 + u03 + u10 + u14 + u32 + u33) : ℕ) : ℝ) < (((n + 1) : ℕ) : ℝ) := by
      push_cast
      linarith only [hgap02b, hgap03b, hgap10b, hgap14b, hgap32b, hgap33b, hdelta1]
    have hnat : (s02 + s03 + s10 + s14 + s32 + s33 + u02 + u03 + u10 + u14 + u32 + u33) < (n + 1) := by exact_mod_cast hreal
    omega
  have hcut46 : (s02 + s03 + s32 + u02 + u03 + u32 + 1) + 1 ≤ (n) := by
    have hreal : (((s02 + s03 + s32 + u02 + u03 + u32 + 1) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [hc13a, htr034a, hgap02b, hgap03b, hnonneg14, hgap32b, hdelta1]
    have hnat : (s02 + s03 + s32 + u02 + u03 + u32 + 1) < (n) := by exact_mod_cast hreal
    omega
  have hcut52 : (s04 + s11 + s33 + u04 + u11 + u33 + 1) + 1 ≤ (n) := by
    have hreal : (((s04 + s11 + s33 + u04 + u11 + u33 + 1) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [ht01, ht12, hc23a, htr012c, htr023c, htr124a, hgap04b, hgap11b, hnonneg31, hgap33b, hnonneg42, hdelta1]
    have hnat : (s04 + s11 + s33 + u04 + u11 + u33 + 1) < (n) := by exact_mod_cast hreal
    omega
  have hcut53 : (s02 + s11 + s14 + u02 + u11 + u14 + 2) + 1 ≤ (n) := by
    have hreal : (((s02 + s11 + s14 + u02 + u11 + u14 + 2) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [hc13a, htr012c, htr034a, htr124a, htr234c, hgap02b, hgap11b, hgap14b, hdelta1]
    have hnat : (s02 + s11 + s14 + u02 + u11 + u14 + 2) < (n) := by exact_mod_cast hreal
    omega
  have hcut8 : (s03 + u03) + 1 ≤ (s13 + 1) := by
    have hreal : (((s03 + u03) : ℕ) : ℝ) < (((s13 + 1) : ℕ) : ℝ) := by
      push_cast
      linarith only [htr023c, htr034a, htr134c, hgap03b, hgap13c]
    have hnat : (s03 + u03) < (s13 + 1) := by exact_mod_cast hreal
    omega
  have hcut32 : (s30 + s32 + s34 + u30 + u32 + u34) + 1 ≤ (n) := by
    have hreal : (((s30 + s32 + s34 + u30 + u32 + u34) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [htr034a, hgap30b, hnonneg31, hgap32b, hgap34b, hdelta1]
    have hnat : (s30 + s32 + s34 + u30 + u32 + u34) < (n) := by exact_mod_cast hreal
    omega
  have hcut26 : (s04 + u04) + 1 ≤ (s14 + 2) := by
    have hreal : (((s04 + u04) : ℕ) : ℝ) < (((s14 + 2) : ℕ) : ℝ) := by
      push_cast
      linarith only [ht01, hgap04b, hgap14c]
    have hnat : (s04 + u04) < (s14 + 2) := by exact_mod_cast hreal
    omega
  have hcut31 : (s31 + u31) + 1 ≤ (s10 + 1) := by
    have hreal : (((s31 + u31) : ℕ) : ℝ) < (((s10 + 1) : ℕ) : ℝ) := by
      push_cast
      linarith only [ht12, hc23a, hgap10c, hgap31b]
    have hnat : (s31 + u31) < (s10 + 1) := by exact_mod_cast hreal
    omega
  have hcut48 : (s03 + s32 + s33 + u03 + u32 + u33 + 1) + 1 ≤ (n) := by
    have hreal : (((s03 + s32 + s33 + u03 + u32 + u33 + 1) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [hc01b, hc13a, htr023c, hgap03b, hgap32b, hgap33b, hdelta1]
    have hnat : (s03 + s32 + s33 + u03 + u32 + u33 + 1) < (n) := by exact_mod_cast hreal
    omega
  have hcut58 : (s40 + s41 + s43 + s44 + u40 + u41 + u43 + u44) + 1 ≤ (n + 1) := by
    have hreal : (((s40 + s41 + s43 + s44 + u40 + u41 + u43 + u44) : ℕ) : ℝ) < (((n + 1) : ℕ) : ℝ) := by
      push_cast
      linarith only [htr234c, hgap40b, hgap41b, hgap43b, hgap44b, hdelta1]
    have hnat : (s40 + s41 + s43 + s44 + u40 + u41 + u43 + u44) < (n + 1) := by exact_mod_cast hreal
    omega
  have hcut15 : (s40 + s41 + s42 + s43 + u40 + u41 + u42 + u43) + 1 ≤ (n + 1) := by
    have hreal : (((s40 + s41 + s42 + s43 + u40 + u41 + u42 + u43) : ℕ) : ℝ) < (((n + 1) : ℕ) : ℝ) := by
      push_cast
      linarith only [hgap40b, hgap41b, hgap42b, hgap43b, hnonneg44, hdelta1]
    have hnat : (s40 + s41 + s42 + s43 + u40 + u41 + u42 + u43) < (n + 1) := by exact_mod_cast hreal
    omega
  have hcut59 : (s33 + s34 + s40 + s42 + u33 + u34 + u40 + u42) + 1 ≤ (n + 1) := by
    have hreal : (((s33 + s34 + s40 + s42 + u33 + u34 + u40 + u42) : ℕ) : ℝ) < (((n + 1) : ℕ) : ℝ) := by
      push_cast
      linarith only [ht34, htr124c, hgap33b, hgap34b, hgap40b, hgap42b, hdelta1]
    have hnat : (s33 + s34 + s40 + s42 + u33 + u34 + u40 + u42) < (n + 1) := by exact_mod_cast hreal
    omega
  have hcut36 : (s01 + s30 + s34 + u01 + u30 + u34 + 1) + 1 ≤ (n) := by
    have hreal : (((s01 + s30 + s34 + u01 + u30 + u34 + 1) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [htr123a, htr124a, htr234c, hgap01b, hgap30b, hgap34b, hnonneg43, hdelta1]
    have hnat : (s01 + s30 + s34 + u01 + u30 + u34 + 1) < (n) := by exact_mod_cast hreal
    omega
  have hcut21 : (s03 + s32 + u03 + u32 + 2) + 1 ≤ (n) := by
    have hreal : (((s03 + s32 + u03 + u32 + 2) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [hc01b, hc13a, htr023c, htr034a, hgap03b, hgap32b, hdelta1]
    have hnat : (s03 + s32 + u03 + u32 + 2) < (n) := by exact_mod_cast hreal
    omega
  have hcut35 : (s30 + s31 + s33 + u30 + u31 + u33 + 1) + 1 ≤ (n) := by
    have hreal : (((s30 + s31 + s33 + u30 + u31 + u33 + 1) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [ht23, hc02b, htr023c, htr134a, hgap30b, hgap31b, hgap33b, hdelta1]
    have hnat : (s30 + s31 + s33 + u30 + u31 + u33 + 1) < (n) := by exact_mod_cast hreal
    omega
  have hcut30 : (s34 + s40 + u34 + u40) + 1 ≤ (n) := by
    have hreal : (((s34 + s40 + u34 + u40) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [ht34, htr034a, htr124c, htr234c, hgap34b, hgap40b, hdelta1]
    have hnat : (s34 + s40 + u34 + u40) < (n) := by exact_mod_cast hreal
    omega
  have hcut40 : (s02 + u02) + 1 ≤ (s34 + 1) := by
    have hreal : (((s02 + u02) : ℕ) : ℝ) < (((s34 + 1) : ℕ) : ℝ) := by
      push_cast
      linarith only [ht23, hc02b, hgap02b, hgap34c]
    have hnat : (s02 + u02) < (s34 + 1) := by exact_mod_cast hreal
    omega
  have hcut27 : (s03 + s33 + u03 + u33 + 3) + 1 ≤ (n) := by
    have hreal : (((s03 + s33 + u03 + u33 + 3) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [ht12, hc01b, hc23a, htr023c, htr123a, htr124a, hgap03b, hgap33b, hnonneg42, hdelta1]
    have hnat : (s03 + s33 + u03 + u33 + 3) < (n) := by exact_mod_cast hreal
    omega
  have hcut13 : (s40 + s41 + s43 + u40 + u41 + u43) + 1 ≤ (n) := by
    have hreal : (((s40 + s41 + s43 + u40 + u41 + u43) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [ht34, hc03b, htr034c, hgap40b, hgap41b, hnonneg42, hgap43b, hdelta1]
    have hnat : (s40 + s41 + s43 + u40 + u41 + u43) < (n) := by exact_mod_cast hreal
    omega
  have hcut50 : (s43 + s44 + u43 + u44 + 1) + 1 ≤ (n) := by
    have hreal : (((s43 + s44 + u43 + u44 + 1) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [ht2a, ht4b, hc23a, htr123a, htr124a, hnonneg42, hgap43b, hgap44b, hdelta1]
    have hnat : (s43 + s44 + u43 + u44 + 1) < (n) := by exact_mod_cast hreal
    omega
  have hcut16 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 2) := by
    have hreal : (((s00 + s44 + u00 + u44) : ℕ) : ℝ) < (((n + 2) : ℕ) : ℝ) := by
      push_cast
      linarith only [ht0a, ht4b, hgap00b, hgap44b, hdelta1]
    have hnat : (s00 + s44 + u00 + u44) < (n + 2) := by exact_mod_cast hreal
    omega
  have hcut22 : (s10 + s32 + u10 + u32 + 1) + 1 ≤ (n) := by
    have hreal : (((s10 + s32 + u10 + u32 + 1) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [hc01b, htr012c, htr023c, htr034a, hgap10b, hgap32b, hdelta1]
    have hnat : (s10 + s32 + u10 + u32 + 1) < (n) := by exact_mod_cast hreal
    omega
  have hcut33 : (s30 + s34 + u30 + u34 + 2) + 1 ≤ (n) := by
    have hreal : (((s30 + s34 + u30 + u34 + 2) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [htr034a, htr123a, htr124a, htr234c, hgap30b, hgap34b, hdelta1]
    have hnat : (s30 + s34 + u30 + u34 + 2) < (n) := by exact_mod_cast hreal
    omega
  have hcut51 : (s12 + s13 + s14 + u12 + u13 + u14 + 1) + 1 ≤ (n) := by
    have hreal : (((s12 + s13 + s14 + u12 + u13 + u14 + 1) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [ht12, hc23a, htr123a, hgap12b, hgap13b, hgap14b, hdelta1]
    have hnat : (s12 + s13 + s14 + u12 + u13 + u14 + 1) < (n) := by exact_mod_cast hreal
    omega
  have hcut0 : (s11 + s12 + s41 + s42 + u11 + u12 + u41 + u42) + 1 ≤ (s32 + 2) := by
    have hreal : (((s11 + s12 + s41 + s42 + u11 + u12 + u41 + u42) : ℕ) : ℝ) < (((s32 + 2) : ℕ) : ℝ) := by
      push_cast
      linarith only [hgap11b, hgap12b, hgap32c, hgap41b, hgap42b]
    have hnat : (s11 + s12 + s41 + s42 + u11 + u12 + u41 + u42) < (s32 + 2) := by exact_mod_cast hreal
    omega
  have hcut3 : (s00 + s04 + s13 + s40 + s44 + u00 + u04 + u13 + u40 + u44) + 1 ≤ (2 * n + 2) := by
    have hreal : (((s00 + s04 + s13 + s40 + s44 + u00 + u04 + u13 + u40 + u44) : ℕ) : ℝ) < (((2 * n + 2) : ℕ) : ℝ) := by
      push_cast
      linarith only [hgap00b, hgap04b, hgap13b, hgap40b, hgap44b, hdelta1]
    have hnat : (s00 + s04 + s13 + s40 + s44 + u00 + u04 + u13 + u40 + u44) < (2 * n + 2) := by exact_mod_cast hreal
    omega
  have hcut45 : (s01 + s43 + u01 + u43) + 1 ≤ (s33 + 2) := by
    have hreal : (((s01 + s43 + u01 + u43) : ℕ) : ℝ) < (((s33 + 2) : ℕ) : ℝ) := by
      push_cast
      linarith only [hgap01b, hgap33c, hgap43b]
    have hnat : (s01 + s43 + u01 + u43) < (s33 + 2) := by exact_mod_cast hreal
    omega
  have hcut23 : (s14 + s32 + u14 + u32 + 1) + 1 ≤ (n) := by
    have hreal : (((s14 + s32 + u14 + u32 + 1) : ℕ) : ℝ) < (((n) : ℕ) : ℝ) := by
      push_cast
      linarith only [hc13a, htr012c, htr023c, htr034a, hgap14b, hgap32b, hdelta1]
    have hnat : (s14 + s32 + u14 + u32 + 1) < (n) := by exact_mod_cast hreal
    omega
  have hcut60 : (s40 + s41 + s42 + s44 + u40 + u41 + u42 + u44) + 1 ≤ (n + 1) := by
    have hreal : (((s40 + s41 + s42 + s44 + u40 + u41 + u42 + u44) : ℕ) : ℝ) < (((n + 1) : ℕ) : ℝ) := by
      push_cast
      linarith only [htr034b, hgap40b, hgap41b, hgap42b, hgap44b, hdelta1]
    have hnat : (s40 + s41 + s42 + s44 + u40 + u41 + u42 + u44) < (n + 1) := by exact_mod_cast hreal
    omega
  have hcut42 : (s30 + s31 + u30 + u31) + 1 ≤ (s10 + 2) := by
    have hreal : (((s30 + s31 + u30 + u31) : ℕ) : ℝ) < (((s10 + 2) : ℕ) : ℝ) := by
      push_cast
      linarith only [ht12, ht23, hgap10c, hgap30b, hgap31b]
    have hnat : (s30 + s31 + u30 + u31) < (s10 + 2) := by exact_mod_cast hreal
    omega
  exact symbolic_mask127_integer_closure n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)

#print axioms symbolic_mask127_probe
end Jsp404.SixExactFloorKernel
