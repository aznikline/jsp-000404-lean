import Jsp000404.SixExactFloorKernelSymbolicMask011NatShard000
import Jsp000404.SixExactFloorKernelSymbolicMask011NatShard001
import Jsp000404.SixExactFloorKernelSymbolicMask011NatShard002
import Jsp000404.SixExactFloorKernelSymbolicMask011NatShard003
import Jsp000404.SixExactFloorKernelSymbolicMask011NatShard004
import Jsp000404.SixExactFloorKernelSymbolicMask011NatShard005
import Jsp000404.SixExactFloorKernelSymbolicMask011NatShard006
import Jsp000404.SixExactFloorKernelSymbolicMask011NatShard007
import Jsp000404.SixExactFloorKernelSymbolicMask011NatShard008

namespace Jsp404.SixExactFloorKernel
private theorem min_score_cases (s u : ℕ) (hmin : u = min s 1) :
    (s = 0 ∧ u = 0) ∨ (1 ≤ s ∧ u = 1) := by omega

set_option maxHeartbeats 16000000 in
theorem symbolic_mask11_integer_closure (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut81 : (s04 + s31 + s32 + s33 + s40 + u04 + u31 + u32 + u33 + u40) + 1 ≤ (2 * n))
    (hcut51 : (s31 + s32 + u31 + u32 + 1) + 1 ≤ (n))
    (hcut49 : (s03 + s32 + u03 + u32 + 1) + 1 ≤ (n))
    (hcut63 : (s04 + s10 + s11 + s12 + s40 + u04 + u10 + u11 + u12 + u40) + 1 ≤ (2 * n))
    (hcut82 : (s04 + s12 + s13 + s30 + s40 + u04 + u12 + u13 + u30 + u40) + 1 ≤ (2 * n + 1))
    (hcut7 : (s00 + s33 + u00 + u33) + 1 ≤ (n + 1))
    (hcut60 : (s10 + s31 + u10 + u31 + 1) + 1 ≤ (n))
    (hcut5 : (s03 + s12 + s14 + s30 + s41 + u03 + u12 + u14 + u30 + u41) + 1 ≤ (n + 2))
    (hcut83 : (s04 + s10 + s11 + s13 + s40 + u04 + u10 + u11 + u13 + u40) + 1 ≤ (2 * n))
    (hcut6 : (s02 + s03 + s10 + s14 + s32 + s41 + u02 + u03 + u10 + u14 + u32 + u41) + 1 ≤ (n))
    (hcut75 : (s03 + s04 + s12 + u03 + u04 + u12) + 1 ≤ (n))
    (hcut8 : (s02 + u02) + 1 ≤ (s12 + 1))
    (hcut35 : (s13 + s43 + u13 + u43 + 2) + 1 ≤ (n))
    (hcut52 : (s14 + s30 + u14 + u30 + 1) + 1 ≤ (n))
    (hcut78 : (s40 + s41 + s44 + u40 + u41 + u44) + 1 ≤ (n + 1))
    (hcut61 : (s10 + s32 + u10 + u32 + 1) + 1 ≤ (n))
    (hcut0 : (s03 + s12 + s30 + s34 + s41 + s42 + s43 + u03 + u12 + u30 + u34 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut79 : (s00 + s04 + s33 + s40 + s44 + u00 + u04 + u33 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut44 : (s10 + s11 + u10 + u11 + 1) + 1 ≤ (n))
    (hcut84 : (s11 + s13 + s14 + s32 + u11 + u13 + u14 + u32) + 1 ≤ (n))
    (hcut1 : (n) + 1 ≤ (s04 + s40 + 4))
    (hcut43 : (s10 + s14 + u10 + u14 + 2) + 1 ≤ (n))
    (hcut54 : (s11 + s12 + u11 + u12 + 1) + 1 ≤ (n))
    (hcut2 : (s10 + s11 + s31 + s32 + u10 + u11 + u31 + u32) + 1 ≤ (s00 + 2))
    (hcut29 : (s01 + s02 + s42 + u01 + u02 + u42) + 1 ≤ (s33 + 1))
    (hcut87 : (s03 + s31 + s32 + u03 + u31 + u32) + 1 ≤ (n))
    (hcut69 : (s10 + s13 + s14 + u10 + u13 + u14 + 1) + 1 ≤ (n))
    (hcut40 : (s00 + s34 + u00 + u34) + 1 ≤ (n + 1))
    (hcut62 : (s04 + s10 + s32 + s33 + s40 + u04 + u10 + u32 + u33 + u40) + 1 ≤ (2 * n))
    (hcut3 : (s00 + s33 + s34 + u00 + u33 + u34) + 1 ≤ (n + 2))
    (hcut47 : (s31 + u31 + 2) + 1 ≤ (n))
    (hcut86 : (s01 + s02 + s32 + u01 + u02 + u32) + 1 ≤ (s12 + 2))
    (hcut48 : (s32 + u32 + 2) + 1 ≤ (n))
    (hcut57 : (s12 + s14 + u12 + u14 + 1) + 1 ≤ (n))
    (hcut55 : (s12 + s14 + s30 + u12 + u14 + u30) + 1 ≤ (n))
    (hcut50 : (s11 + u11 + 2) + 1 ≤ (n))
    (hcut90 : (s01 + s02 + s13 + s42 + s43 + u01 + u02 + u13 + u42 + u43) + 1 ≤ (s33 + 2))
    (hcut92 : (s11 + s13 + s14 + s31 + u11 + u13 + u14 + u31 + 1) + 1 ≤ (n))
    (hcut94 : (s03 + s10 + s11 + u03 + u10 + u11) + 1 ≤ (n))
    (hcut95 : (s03 + s14 + s30 + u03 + u14 + u30) + 1 ≤ (n + 1))
    (hcut96 : (s10 + s13 + s14 + s31 + s32 + u10 + u13 + u14 + u31 + u32) + 1 ≤ (n + 1))
    (hcut97 : (s02 + s03 + s10 + s14 + s31 + u02 + u03 + u10 + u14 + u31) + 1 ≤ (n))
    (hcut98 : (s00 + s01 + s03 + s04 + u00 + u01 + u03 + u04) + 1 ≤ (n + 1))
    (hcut99 : (s03 + s11 + s12 + s14 + u03 + u11 + u12 + u14) + 1 ≤ (n))
    (hcut100 : (s40 + s41 + s42 + u40 + u41 + u42) + 1 ≤ (n))
    (hcut101 : (s10 + s11 + s14 + s41 + u10 + u11 + u14 + u41) + 1 ≤ (n))
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
  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
  ·
    have hcase00 : (s00 = 0 ∧ u00 = 0) ∨ (1 ≤ s00 ∧ u00 = 1) := Or.inl ⟨hcase000a, hcase000b⟩
    exact symbolic_mask11_integer_shard000 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut81 hcut51 hcut49 hcut63 hcut82 hcut7 hcut60 hcut5 hcut83 hcut6 hcut75 hcut8 hcut35 hcut52 hcut78 hcut61 hcut0 hcut79 hcut44 hcut84 hcut1 hcut43 hcut54 hcut2 hcut29 hcut87 hcut69 hcut40 hcut62 hcut3 hcut47 hcut86 hcut48 hcut57 hcut55 hcut50 hcut90 hcut92 hcut94 hcut95 hcut96 hcut97 hcut98 hcut99 hcut100 hcut101 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase000a hcase000b
  ·
    have hcase00 : (s00 = 0 ∧ u00 = 0) ∨ (1 ≤ s00 ∧ u00 = 1) := Or.inr ⟨hcase001a, hcase001b⟩
    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
    ·
      have hcase03 : (s03 = 0 ∧ u03 = 0) ∨ (1 ≤ s03 ∧ u03 = 1) := Or.inl ⟨hcase030a, hcase030b⟩
      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
      ·
        have hcase11 : (s11 = 0 ∧ u11 = 0) ∨ (1 ≤ s11 ∧ u11 = 1) := Or.inl ⟨hcase110a, hcase110b⟩
        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
        ·
          have hcase10 : (s10 = 0 ∧ u10 = 0) ∨ (1 ≤ s10 ∧ u10 = 1) := Or.inl ⟨hcase100a, hcase100b⟩
          exact symbolic_mask11_integer_shard001 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut81 hcut51 hcut49 hcut63 hcut82 hcut7 hcut60 hcut5 hcut83 hcut6 hcut75 hcut8 hcut35 hcut52 hcut78 hcut61 hcut0 hcut79 hcut44 hcut84 hcut1 hcut43 hcut54 hcut2 hcut29 hcut87 hcut69 hcut40 hcut62 hcut3 hcut47 hcut86 hcut48 hcut57 hcut55 hcut50 hcut90 hcut92 hcut94 hcut95 hcut96 hcut97 hcut98 hcut99 hcut100 hcut101 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase001a hcase001b hcase030a hcase030b hcase110a hcase110b hcase100a hcase100b
        ·
          have hcase10 : (s10 = 0 ∧ u10 = 0) ∨ (1 ≤ s10 ∧ u10 = 1) := Or.inr ⟨hcase101a, hcase101b⟩
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            have hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1) := Or.inl ⟨hcase040a, hcase040b⟩
            exact symbolic_mask11_integer_shard002 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut81 hcut51 hcut49 hcut63 hcut82 hcut7 hcut60 hcut5 hcut83 hcut6 hcut75 hcut8 hcut35 hcut52 hcut78 hcut61 hcut0 hcut79 hcut44 hcut84 hcut1 hcut43 hcut54 hcut2 hcut29 hcut87 hcut69 hcut40 hcut62 hcut3 hcut47 hcut86 hcut48 hcut57 hcut55 hcut50 hcut90 hcut92 hcut94 hcut95 hcut96 hcut97 hcut98 hcut99 hcut100 hcut101 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase001a hcase001b hcase030a hcase030b hcase110a hcase110b hcase101a hcase101b hcase040a hcase040b
          ·
            have hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1) := Or.inr ⟨hcase041a, hcase041b⟩
            exact symbolic_mask11_integer_shard003 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut81 hcut51 hcut49 hcut63 hcut82 hcut7 hcut60 hcut5 hcut83 hcut6 hcut75 hcut8 hcut35 hcut52 hcut78 hcut61 hcut0 hcut79 hcut44 hcut84 hcut1 hcut43 hcut54 hcut2 hcut29 hcut87 hcut69 hcut40 hcut62 hcut3 hcut47 hcut86 hcut48 hcut57 hcut55 hcut50 hcut90 hcut92 hcut94 hcut95 hcut96 hcut97 hcut98 hcut99 hcut100 hcut101 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase001a hcase001b hcase030a hcase030b hcase110a hcase110b hcase101a hcase101b hcase041a hcase041b
      ·
        have hcase11 : (s11 = 0 ∧ u11 = 0) ∨ (1 ≤ s11 ∧ u11 = 1) := Or.inr ⟨hcase111a, hcase111b⟩
        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
        ·
          have hcase12 : (s12 = 0 ∧ u12 = 0) ∨ (1 ≤ s12 ∧ u12 = 1) := Or.inl ⟨hcase120a, hcase120b⟩
          exact symbolic_mask11_integer_shard004 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut81 hcut51 hcut49 hcut63 hcut82 hcut7 hcut60 hcut5 hcut83 hcut6 hcut75 hcut8 hcut35 hcut52 hcut78 hcut61 hcut0 hcut79 hcut44 hcut84 hcut1 hcut43 hcut54 hcut2 hcut29 hcut87 hcut69 hcut40 hcut62 hcut3 hcut47 hcut86 hcut48 hcut57 hcut55 hcut50 hcut90 hcut92 hcut94 hcut95 hcut96 hcut97 hcut98 hcut99 hcut100 hcut101 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase001a hcase001b hcase030a hcase030b hcase111a hcase111b hcase120a hcase120b
        ·
          have hcase12 : (s12 = 0 ∧ u12 = 0) ∨ (1 ≤ s12 ∧ u12 = 1) := Or.inr ⟨hcase121a, hcase121b⟩
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            have hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1) := Or.inl ⟨hcase040a, hcase040b⟩
            exact symbolic_mask11_integer_shard005 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut81 hcut51 hcut49 hcut63 hcut82 hcut7 hcut60 hcut5 hcut83 hcut6 hcut75 hcut8 hcut35 hcut52 hcut78 hcut61 hcut0 hcut79 hcut44 hcut84 hcut1 hcut43 hcut54 hcut2 hcut29 hcut87 hcut69 hcut40 hcut62 hcut3 hcut47 hcut86 hcut48 hcut57 hcut55 hcut50 hcut90 hcut92 hcut94 hcut95 hcut96 hcut97 hcut98 hcut99 hcut100 hcut101 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase001a hcase001b hcase030a hcase030b hcase111a hcase111b hcase121a hcase121b hcase040a hcase040b
          ·
            have hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1) := Or.inr ⟨hcase041a, hcase041b⟩
            exact symbolic_mask11_integer_shard006 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut81 hcut51 hcut49 hcut63 hcut82 hcut7 hcut60 hcut5 hcut83 hcut6 hcut75 hcut8 hcut35 hcut52 hcut78 hcut61 hcut0 hcut79 hcut44 hcut84 hcut1 hcut43 hcut54 hcut2 hcut29 hcut87 hcut69 hcut40 hcut62 hcut3 hcut47 hcut86 hcut48 hcut57 hcut55 hcut50 hcut90 hcut92 hcut94 hcut95 hcut96 hcut97 hcut98 hcut99 hcut100 hcut101 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase001a hcase001b hcase030a hcase030b hcase111a hcase111b hcase121a hcase121b hcase041a hcase041b
    ·
      have hcase03 : (s03 = 0 ∧ u03 = 0) ∨ (1 ≤ s03 ∧ u03 = 1) := Or.inr ⟨hcase031a, hcase031b⟩
      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
      ·
        have hcase40 : (s40 = 0 ∧ u40 = 0) ∨ (1 ≤ s40 ∧ u40 = 1) := Or.inl ⟨hcase400a, hcase400b⟩
        exact symbolic_mask11_integer_shard007 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut81 hcut51 hcut49 hcut63 hcut82 hcut7 hcut60 hcut5 hcut83 hcut6 hcut75 hcut8 hcut35 hcut52 hcut78 hcut61 hcut0 hcut79 hcut44 hcut84 hcut1 hcut43 hcut54 hcut2 hcut29 hcut87 hcut69 hcut40 hcut62 hcut3 hcut47 hcut86 hcut48 hcut57 hcut55 hcut50 hcut90 hcut92 hcut94 hcut95 hcut96 hcut97 hcut98 hcut99 hcut100 hcut101 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase001a hcase001b hcase031a hcase031b hcase400a hcase400b
      ·
        have hcase40 : (s40 = 0 ∧ u40 = 0) ∨ (1 ≤ s40 ∧ u40 = 1) := Or.inr ⟨hcase401a, hcase401b⟩
        exact symbolic_mask11_integer_shard008 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut81 hcut51 hcut49 hcut63 hcut82 hcut7 hcut60 hcut5 hcut83 hcut6 hcut75 hcut8 hcut35 hcut52 hcut78 hcut61 hcut0 hcut79 hcut44 hcut84 hcut1 hcut43 hcut54 hcut2 hcut29 hcut87 hcut69 hcut40 hcut62 hcut3 hcut47 hcut86 hcut48 hcut57 hcut55 hcut50 hcut90 hcut92 hcut94 hcut95 hcut96 hcut97 hcut98 hcut99 hcut100 hcut101 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase001a hcase001b hcase031a hcase031b hcase401a hcase401b

#print axioms symbolic_mask11_integer_closure
end Jsp404.SixExactFloorKernel
