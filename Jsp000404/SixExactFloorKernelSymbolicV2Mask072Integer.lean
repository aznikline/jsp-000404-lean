import Jsp000404.SixExactFloorKernelSymbolicV2Mask072NatShard000

namespace Jsp404.SixExactFloorKernel
private theorem min_score_cases (s u : ℕ) (hmin : u = min s 1) :
    (s = 0 ∧ u = 0) ∨ (1 ≤ s ∧ u = 1) := by omega

set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask72_integer_closure (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut68 : (s00 + s04 + s40 + s44 + u00 + u04 + u40 + u44) + 1 ≤ (2 * n))
    (hcut24 : (s12 + u12) + 1 ≤ (s33 + 1))
    (hcut18 : (s43 + s44 + u43 + u44 + 1) + 1 ≤ (n))
    (hcut90 : (s01 + s02 + s10 + s14 + u01 + u02 + u10 + u14) + 1 ≤ (n + 1))
    (hcut88 : (s00 + s02 + s03 + s04 + u00 + u02 + u03 + u04) + 1 ≤ (n + 1))
    (hcut64 : (s00 + s32 + s33 + u00 + u32 + u33) + 1 ≤ (n + 1))
    (hcut60 : (s01 + s02 + s03 + s10 + u01 + u02 + u03 + u10) + 1 ≤ (n + 1))
    (hcut89 : (s00 + s01 + s14 + s41 + u00 + u01 + u14 + u41) + 1 ≤ (n + 2))
    (hcut61 : (s00 + s32 + u00 + u32) + 1 ≤ (n))
    (hcut59 : (s00 + s01 + s02 + s13 + u00 + u01 + u02 + u13) + 1 ≤ (n + 1))
    (hcut6 : (s14 + s40 + s41 + s44 + u14 + u40 + u41 + u44) + 1 ≤ (n + s34 + 3))
    (hcut56 : (s02 + s30 + u02 + u30) + 1 ≤ (n))
    (hcut3 : (s02 + s03 + s30 + s31 + s34 + s41 + s42 + s43 + u02 + u03 + u30 + u31 + u34 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut62 : (s00 + s33 + u00 + u33) + 1 ≤ (n))
    (hcut85 : (s04 + s13 + s30 + s31 + s32 + s40 + u04 + u13 + u30 + u31 + u32 + u40) + 1 ≤ (2 * n + 1))
    (hcut58 : (s00 + s01 + s03 + u00 + u01 + u03) + 1 ≤ (n + 1))
    (hcut87 : (s00 + s34 + s41 + u00 + u34 + u41) + 1 ≤ (n + 2))
    (hcut33 : (s40 + s42 + u40 + u42) + 1 ≤ (n))
    (hcut79 : (s04 + s30 + s31 + u04 + u30 + u31) + 1 ≤ (n + 1))
    (hcut82 : (s03 + s04 + s30 + u03 + u04 + u30) + 1 ≤ (n))
    (hcut40 : (s40 + s41 + u40 + u41) + 1 ≤ (n))
    (hcut86 : (s14 + s30 + s31 + s32 + s33 + s40 + u14 + u30 + u31 + u32 + u33 + u40) + 1 ≤ (2 * n + 1))
    (hcut81 : (s01 + s04 + s10 + s40 + s43 + u01 + u04 + u10 + u40 + u43) + 1 ≤ (2 * n))
    (hcut55 : (s02 + s31 + u02 + u31) + 1 ≤ (n))
    (hcut91 : (s00 + s04 + s11 + s40 + s44 + u00 + u04 + u11 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut13 : (s11 + s43 + u11 + u43 + 1) + 1 ≤ (n))
    (hcut4 : (s00 + s11 + s33 + s44 + u00 + u11 + u33 + u44) + 1 ≤ (n + 2))
    (hcut32 : (s03 + s04 + u03 + u04 + 1) + 1 ≤ (n))
    (hcut5 : (s10 + u10) + 1 ≤ (s00 + 2))
    (hcut44 : (s01 + s02 + u01 + u02 + 1) + 1 ≤ (n))
    (hcut80 : (s00 + s04 + s33 + s40 + s44 + u00 + u04 + u33 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut52 : (s00 + s43 + u00 + u43 + 1) + 1 ≤ (n))
    (hcut0 : (s12 + s13 + s42 + s43 + u12 + u13 + u42 + u43) + 1 ≤ (s33 + 2))
    (hcut54 : (s00 + s01 + u00 + u01) + 1 ≤ (n))
    (hcut67 : (s00 + s04 + s40 + u00 + u04 + u40 + 1) + 1 ≤ (2 * n))
    (hcut29 : (s04 + s40 + u04 + u40) + 1 ≤ (n + 2))
    (hcut65 : (s00 + s11 + s34 + u00 + u11 + u34) + 1 ≤ (n + 1))
    (hcut53 : (s00 + s02 + u00 + u02) + 1 ≤ (n))
    (hcut83 : (s03 + s04 + s31 + u03 + u04 + u31) + 1 ≤ (n))
    (hcut2 : (s00 + s04 + s11 + s33 + s34 + s40 + u00 + u04 + u11 + u33 + u34 + u40) + 1 ≤ (2 * n + 2))
    (hcut36 : (s01 + s32 + u01 + u32) + 1 ≤ (s11 + 2))
    (hcut66 : (s00 + s03 + s34 + u00 + u03 + u34) + 1 ≤ (n + 2))
    (hcut50 : (s01 + s02 + s03 + s04 + u01 + u02 + u03 + u04) + 1 ≤ (n))
    (hmincount0 : u00 + (u01 + (u02 + (u03 + (u04)))) ≤ 2)
    (hmincount1 : u10 + (u11 + (u12 + (u13 + (u14)))) ≤ 3)
    (hmincount3 : u30 + (u31 + (u32 + (u33 + (u34)))) ≤ 3)
    (hmincount4 : u40 + (u41 + (u42 + (u43 + (u44)))) ≤ 2)
    (hminend0 : u01 + (u02 + (u03 + (u04))) ≤ 1)
    (hminend4 : u40 + (u41 + (u42 + (u43))) ≤ 1)
    (hmin00 : u00 = min s00 1)
    (hmin01 : u01 = min s01 1)
    (hmin02 : u02 = min s02 1)
    (hmin03 : u03 = min s03 1)
    (hmin04 : u04 = min s04 1)
    (hmin10 : u10 = min s10 1)
    (hmin11 : u11 = min s11 1)
    (hmin12 : u12 = min s12 1)
    (hmin13 : u13 = min s13 1)
    (hmin14 : u14 = min s14 1)
    (hmin30 : u30 = min s30 1)
    (hmin31 : u31 = min s31 1)
    (hmin32 : u32 = min s32 1)
    (hmin33 : u33 = min s33 1)
    (hmin34 : u34 = min s34 1)
    (hmin40 : u40 = min s40 1)
    (hmin41 : u41 = min s41 1)
    (hmin42 : u42 = min s42 1)
    (hmin43 : u43 = min s43 1)
    (hmin44 : u44 = min s44 1)
    : False := by
  have hu00b : u00 ≤ 1 := by rw [hmin00]; exact Nat.min_le_right _ _
  have hu00c : u00 ≤ s00 := by rw [hmin00]; exact Nat.min_le_left _ _
  have hcase00 := min_score_cases s00 u00 hmin00
  have hu01b : u01 ≤ 1 := by rw [hmin01]; exact Nat.min_le_right _ _
  have hu01c : u01 ≤ s01 := by rw [hmin01]; exact Nat.min_le_left _ _
  have hcase01 := min_score_cases s01 u01 hmin01
  have hu02b : u02 ≤ 1 := by rw [hmin02]; exact Nat.min_le_right _ _
  have hu02c : u02 ≤ s02 := by rw [hmin02]; exact Nat.min_le_left _ _
  have hcase02 := min_score_cases s02 u02 hmin02
  have hu03b : u03 ≤ 1 := by rw [hmin03]; exact Nat.min_le_right _ _
  have hu03c : u03 ≤ s03 := by rw [hmin03]; exact Nat.min_le_left _ _
  have hcase03 := min_score_cases s03 u03 hmin03
  have hu04b : u04 ≤ 1 := by rw [hmin04]; exact Nat.min_le_right _ _
  have hu04c : u04 ≤ s04 := by rw [hmin04]; exact Nat.min_le_left _ _
  have hcase04 := min_score_cases s04 u04 hmin04
  have hu10b : u10 ≤ 1 := by rw [hmin10]; exact Nat.min_le_right _ _
  have hu10c : u10 ≤ s10 := by rw [hmin10]; exact Nat.min_le_left _ _
  have hcase10 := min_score_cases s10 u10 hmin10
  have hu11b : u11 ≤ 1 := by rw [hmin11]; exact Nat.min_le_right _ _
  have hu11c : u11 ≤ s11 := by rw [hmin11]; exact Nat.min_le_left _ _
  have hcase11 := min_score_cases s11 u11 hmin11
  have hu12b : u12 ≤ 1 := by rw [hmin12]; exact Nat.min_le_right _ _
  have hu12c : u12 ≤ s12 := by rw [hmin12]; exact Nat.min_le_left _ _
  have hcase12 := min_score_cases s12 u12 hmin12
  have hu13b : u13 ≤ 1 := by rw [hmin13]; exact Nat.min_le_right _ _
  have hu13c : u13 ≤ s13 := by rw [hmin13]; exact Nat.min_le_left _ _
  have hcase13 := min_score_cases s13 u13 hmin13
  have hu14b : u14 ≤ 1 := by rw [hmin14]; exact Nat.min_le_right _ _
  have hu14c : u14 ≤ s14 := by rw [hmin14]; exact Nat.min_le_left _ _
  have hcase14 := min_score_cases s14 u14 hmin14
  have hu30b : u30 ≤ 1 := by rw [hmin30]; exact Nat.min_le_right _ _
  have hu30c : u30 ≤ s30 := by rw [hmin30]; exact Nat.min_le_left _ _
  have hcase30 := min_score_cases s30 u30 hmin30
  have hu31b : u31 ≤ 1 := by rw [hmin31]; exact Nat.min_le_right _ _
  have hu31c : u31 ≤ s31 := by rw [hmin31]; exact Nat.min_le_left _ _
  have hcase31 := min_score_cases s31 u31 hmin31
  have hu32b : u32 ≤ 1 := by rw [hmin32]; exact Nat.min_le_right _ _
  have hu32c : u32 ≤ s32 := by rw [hmin32]; exact Nat.min_le_left _ _
  have hcase32 := min_score_cases s32 u32 hmin32
  have hu33b : u33 ≤ 1 := by rw [hmin33]; exact Nat.min_le_right _ _
  have hu33c : u33 ≤ s33 := by rw [hmin33]; exact Nat.min_le_left _ _
  have hcase33 := min_score_cases s33 u33 hmin33
  have hu34b : u34 ≤ 1 := by rw [hmin34]; exact Nat.min_le_right _ _
  have hu34c : u34 ≤ s34 := by rw [hmin34]; exact Nat.min_le_left _ _
  have hcase34 := min_score_cases s34 u34 hmin34
  have hu40b : u40 ≤ 1 := by rw [hmin40]; exact Nat.min_le_right _ _
  have hu40c : u40 ≤ s40 := by rw [hmin40]; exact Nat.min_le_left _ _
  have hcase40 := min_score_cases s40 u40 hmin40
  have hu41b : u41 ≤ 1 := by rw [hmin41]; exact Nat.min_le_right _ _
  have hu41c : u41 ≤ s41 := by rw [hmin41]; exact Nat.min_le_left _ _
  have hcase41 := min_score_cases s41 u41 hmin41
  have hu42b : u42 ≤ 1 := by rw [hmin42]; exact Nat.min_le_right _ _
  have hu42c : u42 ≤ s42 := by rw [hmin42]; exact Nat.min_le_left _ _
  have hcase42 := min_score_cases s42 u42 hmin42
  have hu43b : u43 ≤ 1 := by rw [hmin43]; exact Nat.min_le_right _ _
  have hu43c : u43 ≤ s43 := by rw [hmin43]; exact Nat.min_le_left _ _
  have hcase43 := min_score_cases s43 u43 hmin43
  have hu44b : u44 ≤ 1 := by rw [hmin44]; exact Nat.min_le_right _ _
  have hu44c : u44 ≤ s44 := by rw [hmin44]; exact Nat.min_le_left _ _
  have hcase44 := min_score_cases s44 u44 hmin44
  clear hmin00 hmin01 hmin02 hmin03 hmin04 hmin10 hmin11 hmin12 hmin13 hmin14 hmin30 hmin31 hmin32 hmin33 hmin34 hmin40 hmin41 hmin42 hmin43 hmin44
  exact symbolic_v2_mask72_integer_shard000 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut68 hcut24 hcut18 hcut90 hcut88 hcut64 hcut60 hcut89 hcut61 hcut59 hcut6 hcut56 hcut3 hcut62 hcut85 hcut58 hcut87 hcut33 hcut79 hcut82 hcut40 hcut86 hcut81 hcut55 hcut91 hcut13 hcut4 hcut32 hcut5 hcut44 hcut80 hcut52 hcut0 hcut54 hcut67 hcut29 hcut65 hcut53 hcut83 hcut2 hcut36 hcut66 hcut50 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44

#print axioms symbolic_v2_mask72_integer_closure
end Jsp404.SixExactFloorKernel
