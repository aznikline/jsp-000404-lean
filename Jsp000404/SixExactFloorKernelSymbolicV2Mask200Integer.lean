import Jsp000404.SixExactFloorKernelSymbolicV2Mask200NatShard000
import Jsp000404.SixExactFloorKernelSymbolicV2Mask200NatShard001
import Jsp000404.SixExactFloorKernelSymbolicV2Mask200NatShard002
import Jsp000404.SixExactFloorKernelSymbolicV2Mask200NatShard003
import Jsp000404.SixExactFloorKernelSymbolicV2Mask200NatShard004
import Jsp000404.SixExactFloorKernelSymbolicV2Mask200NatShard005
import Jsp000404.SixExactFloorKernelSymbolicV2Mask200NatShard006
import Jsp000404.SixExactFloorKernelSymbolicV2Mask200NatShard007
import Jsp000404.SixExactFloorKernelSymbolicV2Mask200NatShard008

namespace Jsp404.SixExactFloorKernel
private theorem min_score_cases (s u : ℕ) (hmin : u = min s 1) :
    (s = 0 ∧ u = 0) ∨ (1 ≤ s ∧ u = 1) := by omega

set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask200_integer_closure (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut2 : (s02 + s03 + s13 + s30 + s31 + s41 + s42 + u02 + u03 + u13 + u30 + u31 + u41 + u42) + 1 ≤ (n))
    (hcut7 : (s00 + s04 + s11 + s33 + s40 + s44 + u00 + u04 + u11 + u33 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut34 : (s13 + u13 + 3) + 1 ≤ (n))
    (hcut26 : (s01 + s32 + u01 + u32) + 1 ≤ (s11 + 2))
    (hcut74 : (s00 + s01 + s04 + s13 + s14 + s40 + u00 + u01 + u04 + u13 + u14 + u40) + 1 ≤ (2 * n + 1))
    (hcut46 : (s00 + s04 + s32 + s40 + u00 + u04 + u32 + u40) + 1 ≤ (2 * n + 1))
    (hcut59 : (s00 + s11 + s44 + u00 + u11 + u44) + 1 ≤ (n + 1))
    (hcut49 : (s11 + s33 + s44 + u11 + u33 + u44) + 1 ≤ (n + 1))
    (hcut57 : (s03 + s31 + u03 + u31 + 2) + 1 ≤ (n))
    (hcut21 : (s40 + s43 + u40 + u43) + 1 ≤ (n))
    (hcut44 : (s14 + s41 + u14 + u41 + 2) + 1 ≤ (n))
    (hcut73 : (s14 + s40 + u14 + u40) + 1 ≤ (n))
    (hcut27 : (s34 + u34) + 1 ≤ (s44 + 2))
    (hcut77 : (s03 + s04 + s10 + u03 + u04 + u10) + 1 ≤ (n + 1))
    (hcut20 : (s00 + s04 + s33 + s40 + u00 + u04 + u33 + u40) + 1 ≤ (2 * n))
    (hcut63 : (s41 + s42 + s44 + u41 + u42 + u44) + 1 ≤ (n))
    (hcut51 : (s02 + s13 + s14 + s30 + u02 + u13 + u14 + u30) + 1 ≤ (n))
    (hcut10 : (s10 + s13 + s14 + s42 + u10 + u13 + u14 + u42) + 1 ≤ (n))
    (hcut71 : (s13 + s14 + s30 + s41 + u13 + u14 + u30 + u41) + 1 ≤ (n))
    (hcut6 : (s04 + s40 + u04 + u40) + 1 ≤ (n + 2))
    (hcut33 : (s30 + s31 + u30 + u31 + 2) + 1 ≤ (n))
    (hcut56 : (s03 + s30 + u03 + u30 + 2) + 1 ≤ (n))
    (hcut3 : (s10 + u10) + 1 ≤ (s00 + 2))
    (hcut0 : (s12 + s43 + u12 + u43) + 1 ≤ (s33 + 2))
    (hcut70 : (s13 + s14 + s31 + s41 + u13 + u14 + u31 + u41) + 1 ≤ (n))
    (hcut58 : (s00 + s11 + s33 + u00 + u11 + u33) + 1 ≤ (n + 1))
    (hcut25 : (s11 + s33 + u11 + u33) + 1 ≤ (n))
    (hcut69 : (s41 + s42 + s43 + s44 + u41 + u42 + u43 + u44) + 1 ≤ (n + 1))
    (hcut78 : (s00 + s03 + s13 + s14 + u00 + u03 + u13 + u14) + 1 ≤ (n + 2))
    (hcut54 : (s01 + s03 + s04 + u01 + u03 + u04) + 1 ≤ (n))
    (hcut68 : (s40 + s41 + s42 + s43 + u40 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut22 : (s42 + u42 + 3) + 1 ≤ (n))
    (hcut47 : (s02 + s13 + s14 + s31 + u02 + u13 + u14 + u31 + 1) + 1 ≤ (n))
    (hcut9 : (s40 + s42 + s43 + s44 + u40 + u42 + u43 + u44) + 1 ≤ (n + 1))
    (hcut19 : (s02 + s03 + u02 + u03 + 2) + 1 ≤ (n))
    (hcut40 : (s40 + s41 + s42 + u40 + u41 + u42) + 1 ≤ (n))
    (hcut37 : (s00 + s33 + s44 + u00 + u33 + u44) + 1 ≤ (n + 1))
    (hcut42 : (s04 + s12 + s40 + s44 + u04 + u12 + u40 + u44) + 1 ≤ (2 * n))
    (hcut1 : (n) + 1 ≤ (s04 + s40 + 4))
    (hcut67 : (s02 + s03 + s04 + u02 + u03 + u04) + 1 ≤ (n))
    (hcut35 : (s00 + s04 + s40 + s44 + u00 + u04 + u40 + u44) + 1 ≤ (2 * n))
    (hcut52 : (s00 + s01 + s02 + u00 + u01 + u02 + 1) + 1 ≤ (n))
    (hcut4 : (s02 + s03 + s30 + s31 + s34 + s41 + s42 + s43 + u02 + u03 + u30 + u31 + u34 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut30 : (s04 + s11 + s40 + s44 + u04 + u11 + u40 + u44) + 1 ≤ (2 * n))
    (hcut45 : (s02 + s13 + s14 + u02 + u13 + u14 + 1) + 1 ≤ (n))
    (hcut53 : (s13 + s14 + s41 + u13 + u14 + u41 + 1) + 1 ≤ (n))
    (hcut43 : (s11 + s34 + u11 + u34) + 1 ≤ (n))
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
  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
  ·
    have hcase01 : (s01 = 0 ∧ u01 = 0) ∨ (1 ≤ s01 ∧ u01 = 1) := Or.inl ⟨hcase010a, hcase010b⟩
    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
    ·
      have hcase02 : (s02 = 0 ∧ u02 = 0) ∨ (1 ≤ s02 ∧ u02 = 1) := Or.inl ⟨hcase020a, hcase020b⟩
      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
      ·
        have hcase03 : (s03 = 0 ∧ u03 = 0) ∨ (1 ≤ s03 ∧ u03 = 1) := Or.inl ⟨hcase030a, hcase030b⟩
        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
        ·
          have hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1) := Or.inl ⟨hcase040a, hcase040b⟩
          exact symbolic_v2_mask200_integer_shard000 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b
        ·
          have hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1) := Or.inr ⟨hcase041a, hcase041b⟩
          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
          ·
            have hcase10 : (s10 = 0 ∧ u10 = 0) ∨ (1 ≤ s10 ∧ u10 = 1) := Or.inl ⟨hcase100a, hcase100b⟩
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              have hcase11 : (s11 = 0 ∧ u11 = 0) ∨ (1 ≤ s11 ∧ u11 = 1) := Or.inl ⟨hcase110a, hcase110b⟩
              exact symbolic_v2_mask200_integer_shard001 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase100a hcase100b hcase110a hcase110b
            ·
              have hcase11 : (s11 = 0 ∧ u11 = 0) ∨ (1 ≤ s11 ∧ u11 = 1) := Or.inr ⟨hcase111a, hcase111b⟩
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                have hcase34 : (s34 = 0 ∧ u34 = 0) ∨ (1 ≤ s34 ∧ u34 = 1) := Or.inl ⟨hcase340a, hcase340b⟩
                exact symbolic_v2_mask200_integer_shard002 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase100a hcase100b hcase111a hcase111b hcase340a hcase340b
              ·
                have hcase34 : (s34 = 0 ∧ u34 = 0) ∨ (1 ≤ s34 ∧ u34 = 1) := Or.inr ⟨hcase341a, hcase341b⟩
                exact symbolic_v2_mask200_integer_shard003 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase100a hcase100b hcase111a hcase111b hcase341a hcase341b
          ·
            have hcase10 : (s10 = 0 ∧ u10 = 0) ∨ (1 ≤ s10 ∧ u10 = 1) := Or.inr ⟨hcase101a, hcase101b⟩
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              have hcase32 : (s32 = 0 ∧ u32 = 0) ∨ (1 ≤ s32 ∧ u32 = 1) := Or.inl ⟨hcase320a, hcase320b⟩
              exact symbolic_v2_mask200_integer_shard004 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase320a hcase320b
            ·
              have hcase32 : (s32 = 0 ∧ u32 = 0) ∨ (1 ≤ s32 ∧ u32 = 1) := Or.inr ⟨hcase321a, hcase321b⟩
              exact symbolic_v2_mask200_integer_shard005 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase321a hcase321b
      ·
        have hcase03 : (s03 = 0 ∧ u03 = 0) ∨ (1 ≤ s03 ∧ u03 = 1) := Or.inr ⟨hcase031a, hcase031b⟩
        exact symbolic_v2_mask200_integer_shard006 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase010a hcase010b hcase020a hcase020b hcase031a hcase031b
    ·
      have hcase02 : (s02 = 0 ∧ u02 = 0) ∨ (1 ≤ s02 ∧ u02 = 1) := Or.inr ⟨hcase021a, hcase021b⟩
      exact symbolic_v2_mask200_integer_shard007 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase010a hcase010b hcase021a hcase021b
  ·
    have hcase01 : (s01 = 0 ∧ u01 = 0) ∨ (1 ≤ s01 ∧ u01 = 1) := Or.inr ⟨hcase011a, hcase011b⟩
    exact symbolic_v2_mask200_integer_shard008 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase011a hcase011b

#print axioms symbolic_v2_mask200_integer_closure
end Jsp404.SixExactFloorKernel
