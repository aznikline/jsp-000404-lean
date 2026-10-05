import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard000
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard001
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard002
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard003
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard004
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard005
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard006
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard007
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard008
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard009
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard010
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard011
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard012
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard013
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard014
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard015
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard016
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard017
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard018
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard019
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard020
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard021
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard022
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard023
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard024
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard025
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard026
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard027
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard028
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard029
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard030
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard031
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard032
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard033
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard034
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard035
import Jsp000404.SixExactFloorKernelSymbolicMask000NatShard036

namespace Jsp404.SixExactFloorKernel
private theorem min_score_cases (s u : ℕ) (hmin : u = min s 1) :
    (s = 0 ∧ u = 0) ∨ (1 ≤ s ∧ u = 1) := by omega

set_option maxHeartbeats 16000000 in
theorem symbolic_mask0_integer_closure (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut120 : (s11 + s12 + s32 + s34 + u11 + u12 + u32 + u34) + 1 ≤ (n))
    (hcut0 : (s00 + s02 + s13 + s31 + s34 + s42 + s43 + u00 + u02 + u13 + u31 + u34 + u42 + u43) + 1 ≤ (n + 2))
    (hcut148 : (s33 + s34 + u33 + u34 + 1) + 1 ≤ (n))
    (hcut1 : (s03 + s30 + s34 + s41 + s42 + s43 + u03 + u30 + u34 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut2 : (s00 + s04 + s11 + s12 + s32 + s33 + s40 + s44 + u00 + u04 + u11 + u12 + u32 + u33 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut3 : (s14 + s40 + s41 + u14 + u40 + u41) + 1 ≤ (n + 2))
    (hcut4 : (s10 + u10) + 1 ≤ (s00 + 2))
    (hcut10 : (s34 + s40 + s42 + s43 + u34 + u40 + u42 + u43) + 1 ≤ (n + 1))
    (hcut14 : (s40 + s41 + s43 + u40 + u41 + u43) + 1 ≤ (n))
    (hcut20 : (s00 + s11 + u00 + u11 + 1) + 1 ≤ (n))
    (hcut25 : (s04 + s31 + s32 + s40 + u04 + u31 + u32 + u40 + 1) + 1 ≤ (2 * n))
    (hcut29 : (s32 + u32 + 2) + 1 ≤ (n))
    (hcut31 : (s33 + u33 + 2) + 1 ≤ (n))
    (hcut32 : (s32 + s33 + u32 + u33 + 1) + 1 ≤ (n))
    (hcut33 : (s11 + u11 + 2) + 1 ≤ (n))
    (hcut35 : (s11 + s33 + u11 + u33 + 1) + 1 ≤ (n))
    (hcut36 : (s11 + s32 + s33 + u11 + u32 + u33) + 1 ≤ (n))
    (hcut37 : (s02 + s13 + s31 + u02 + u13 + u31) + 1 ≤ (n))
    (hcut38 : (s04 + s13 + s30 + s31 + s40 + u04 + u13 + u30 + u31 + u40) + 1 ≤ (2 * n + 1))
    (hcut39 : (s13 + s14 + s30 + s31 + u13 + u14 + u30 + u31) + 1 ≤ (n + 1))
    (hcut43 : (s04 + s30 + s42 + s44 + u04 + u30 + u42 + u44) + 1 ≤ (2 * n + 1))
    (hcut44 : (s14 + s30 + s41 + u14 + u30 + u41) + 1 ≤ (n + 1))
    (hcut46 : (s11 + s12 + s44 + u11 + u12 + u44) + 1 ≤ (n))
    (hcut47 : (s13 + s30 + s44 + u13 + u30 + u44) + 1 ≤ (n + 2))
    (hcut48 : (s04 + s40 + s44 + u04 + u40 + u44 + 2) + 1 ≤ (2 * n))
    (hcut49 : (s31 + s44 + u31 + u44) + 1 ≤ (n))
    (hcut51 : (s12 + u12 + 2) + 1 ≤ (n))
    (hcut52 : (s11 + s12 + u11 + u12 + 1) + 1 ≤ (n))
    (hcut54 : (s12 + s13 + u12 + u13 + 1) + 1 ≤ (n))
    (hcut55 : (s11 + s12 + s13 + u11 + u12 + u13) + 1 ≤ (n))
    (hcut60 : (s00 + s31 + u00 + u31) + 1 ≤ (n))
    (hcut62 : (s10 + u10 + 2) + 1 ≤ (n))
    (hcut64 : (s00 + s02 + u00 + u02) + 1 ≤ (n))
    (hcut65 : (s00 + s12 + u00 + u12 + 1) + 1 ≤ (n))
    (hcut69 : (s01 + u01) + 1 ≤ (s11 + 2))
    (hcut72 : (s10 + s33 + s44 + u10 + u33 + u44) + 1 ≤ (n))
    (hcut73 : (s00 + s12 + s32 + s44 + u00 + u12 + u32 + u44) + 1 ≤ (n))
    (hcut74 : (s00 + s11 + s32 + s44 + u00 + u11 + u32 + u44) + 1 ≤ (n + 1))
    (hcut76 : (s01 + s02 + s10 + s41 + s44 + u01 + u02 + u10 + u41 + u44) + 1 ≤ (n + 2))
    (hcut79 : (s01 + s04 + s13 + s34 + s40 + u01 + u04 + u13 + u34 + u40) + 1 ≤ (2 * n + 1))
    (hcut77 : (s01 + s02 + s03 + s10 + s41 + u01 + u02 + u03 + u10 + u41) + 1 ≤ (n + 1))
    (hcut78 : (s00 + s01 + s02 + s13 + s43 + s44 + u00 + u01 + u02 + u13 + u43 + u44) + 1 ≤ (n + 2))
    (hcut80 : (s04 + s11 + s13 + s34 + s40 + u04 + u11 + u13 + u34 + u40) + 1 ≤ (2 * n + 1))
    (hcut81 : (s00 + s32 + u00 + u32 + 1) + 1 ≤ (n))
    (hcut82 : (s00 + s02 + s03 + u00 + u02 + u03) + 1 ≤ (n + 1))
    (hcut83 : (s00 + s04 + s11 + s32 + s40 + u00 + u04 + u11 + u32 + u40) + 1 ≤ (2 * n))
    (hcut106 : (s00 + s04 + s31 + s40 + s44 + u00 + u04 + u31 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut84 : (s40 + s41 + s42 + u40 + u41 + u42) + 1 ≤ (n))
    (hcut85 : (s00 + s02 + s04 + s31 + s33 + s40 + s44 + u00 + u02 + u04 + u31 + u33 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut86 : (s02 + s04 + s31 + s32 + s40 + s44 + u02 + u04 + u31 + u32 + u40 + u44) + 1 ≤ (2 * n))
    (hcut88 : (s03 + s14 + s30 + u03 + u14 + u30) + 1 ≤ (n + 1))
    (hcut89 : (s02 + s03 + u02 + u03) + 1 ≤ (n))
    (hcut90 : (s40 + s42 + s44 + u40 + u42 + u44) + 1 ≤ (n + 1))
    (hcut91 : (s31 + s42 + s44 + u31 + u42 + u44) + 1 ≤ (n + 1))
    (hcut92 : (s01 + s02 + s03 + s14 + u01 + u02 + u03 + u14) + 1 ≤ (n + 1))
    (hcut93 : (s34 + u34 + 2) + 1 ≤ (n))
    (hcut94 : (s04 + s33 + s40 + s44 + u04 + u33 + u40 + u44 + 1) + 1 ≤ (2 * n))
    (hcut95 : (s34 + s42 + u34 + u42) + 1 ≤ (n))
    (hcut96 : (s32 + s33 + s44 + u32 + u33 + u44) + 1 ≤ (n))
    (hcut107 : (s34 + s40 + s41 + u34 + u40 + u41) + 1 ≤ (n + 1))
    (hcut98 : (s13 + s31 + s44 + u13 + u31 + u44) + 1 ≤ (n + 1))
    (hcut99 : (s04 + s11 + s34 + s40 + u04 + u11 + u34 + u40 + 1) + 1 ≤ (2 * n))
    (hcut100 : (s04 + s11 + s33 + s40 + s44 + u04 + u11 + u33 + u40 + u44) + 1 ≤ (2 * n))
    (hcut101 : (s31 + s43 + s44 + u31 + u43 + u44) + 1 ≤ (n + 1))
    (hcut102 : (s04 + s11 + s32 + s33 + s40 + s44 + u04 + u11 + u32 + u33 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut103 : (s00 + s02 + s04 + s40 + s44 + u00 + u02 + u04 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut104 : (s00 + u00) + 1 ≤ (s10 + 3))
    (hcut105 : (s01 + s02 + s14 + s41 + u01 + u02 + u14 + u41) + 1 ≤ (s04 + s30 + 5))
    (hcut108 : (s03 + s10 + s14 + s41 + u03 + u10 + u14 + u41) + 1 ≤ (n + 1))
    (hcut109 : (s01 + s03 + s10 + s14 + u01 + u03 + u10 + u14) + 1 ≤ (n + 1))
    (hcut111 : (s01 + s31 + s32 + u01 + u31 + u32 + 1) + 1 ≤ (n))
    (hcut112 : (s11 + s34 + u11 + u34 + 1) + 1 ≤ (n))
    (hcut113 : (s31 + s42 + s43 + s44 + u31 + u42 + u43 + u44) + 1 ≤ (n + 1))
    (hcut114 : (s02 + s04 + u02 + u04) + 1 ≤ (n))
    (hcut131 : (s04 + s11 + s12 + s33 + s40 + u04 + u11 + u12 + u33 + u40) + 1 ≤ (2 * n))
    (hcut115 : (s00 + s11 + s33 + s44 + u00 + u11 + u33 + u44) + 1 ≤ (n + 1))
    (hcut116 : (s12 + s33 + s44 + u12 + u33 + u44) + 1 ≤ (n))
    (hcut117 : (s11 + s12 + s33 + s44 + u11 + u12 + u33 + u44) + 1 ≤ (n + 1))
    (hcut118 : (s12 + s34 + u12 + u34 + 1) + 1 ≤ (n))
    (hcut119 : (s01 + s31 + s32 + s43 + s44 + u01 + u31 + u32 + u43 + u44) + 1 ≤ (n + 2))
    (hcut121 : (s32 + s34 + u32 + u34 + 1) + 1 ≤ (n))
    (hcut132 : (s01 + s02 + s04 + s34 + s40 + u01 + u02 + u04 + u34 + u40) + 1 ≤ (2 * n))
    (hcut123 : (s00 + s01 + s03 + u00 + u01 + u03) + 1 ≤ (n + 1))
    (hcut124 : (s10 + s11 + s32 + u10 + u11 + u32) + 1 ≤ (n))
    (hcut125 : (s00 + s11 + s12 + s32 + u00 + u11 + u12 + u32) + 1 ≤ (n))
    (hcut126 : (s10 + s13 + s31 + u10 + u13 + u31) + 1 ≤ (n + 1))
    (hcut140 : (s04 + s10 + s11 + s12 + s40 + u04 + u10 + u11 + u12 + u40) + 1 ≤ (2 * n))
    (hcut127 : (s00 + s11 + s12 + s33 + u00 + u11 + u12 + u33) + 1 ≤ (n + 1))
    (hcut128 : (s10 + s33 + u10 + u33 + 1) + 1 ≤ (n))
    (hcut129 : (s10 + s11 + s33 + u10 + u11 + u33) + 1 ≤ (n))
    (hcut149 : (s01 + s10 + s13 + s31 + u01 + u10 + u13 + u31) + 1 ≤ (n + 1))
    (hcut130 : (s43 + u43) + 1 ≤ (s33 + 2))
    (hcut133 : (s04 + s12 + s32 + s33 + s40 + u04 + u12 + u32 + u33 + u40 + 1) + 1 ≤ (2 * n))
    (hcut134 : (s10 + s32 + s33 + u10 + u32 + u33) + 1 ≤ (n))
    (hcut135 : (s00 + s12 + s13 + u00 + u12 + u13) + 1 ≤ (n))
    (hcut136 : (s10 + s11 + s12 + s13 + u10 + u11 + u12 + u13) + 1 ≤ (n + 1))
    (hcut137 : (s00 + s11 + s32 + s33 + u00 + u11 + u32 + u33) + 1 ≤ (n + 1))
    (hcut138 : (s00 + s04 + s13 + u00 + u04 + u13) + 1 ≤ (n + s41 + 2))
    (hcut139 : (s01 + s02 + s03 + s10 + s14 + u01 + u02 + u03 + u10 + u14) + 1 ≤ (n + 1))
    (hcut143 : (s01 + s13 + s14 + s31 + u01 + u13 + u14 + u31) + 1 ≤ (n + 1))
    (hcut144 : (s01 + s04 + s10 + s40 + s44 + u01 + u04 + u10 + u40 + u44) + 1 ≤ (2 * n))
    (hcut142 : (s31 + s40 + s42 + s43 + s44 + u31 + u40 + u42 + u43 + u44) + 1 ≤ (n + s03 + 3))
    (hcut145 : (s01 + s10 + s14 + s41 + u01 + u10 + u14 + u41) + 1 ≤ (n + 1))
    (hcut146 : (s01 + s02 + s10 + s14 + s41 + u01 + u02 + u10 + u14 + u41) + 1 ≤ (n + 1))
    (hcut151 : (s00 + s04 + s34 + s40 + u00 + u04 + u34 + u40 + 1) + 1 ≤ (2 * n))
    (hcut147 : (s01 + s02 + s10 + s14 + s41 + u01 + u02 + u10 + u14 + u41) + 1 ≤ (s04 + s30 + 5))
    (hcut150 : (s01 + s02 + s04 + s10 + s13 + s31 + u01 + u02 + u04 + u10 + u13 + u31) + 1 ≤ (n + s41 + 3))
    (hcut152 : (s11 + s33 + s34 + u11 + u33 + u34) + 1 ≤ (n))
    (hcut153 : (s12 + s32 + s33 + s34 + u12 + u32 + u33 + u34) + 1 ≤ (n))
    (hcut154 : (s11 + s32 + s33 + s34 + u11 + u32 + u33 + u34) + 1 ≤ (n + 1))
    (hcut155 : (s11 + s12 + s32 + s33 + s34 + u11 + u12 + u32 + u33 + u34) + 1 ≤ (n + 1))
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
  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
  ·
    have hcase02 : (s02 = 0 ∧ u02 = 0) ∨ (1 ≤ s02 ∧ u02 = 1) := Or.inl ⟨hcase020a, hcase020b⟩
    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
    ·
      have hcase01 : (s01 = 0 ∧ u01 = 0) ∨ (1 ≤ s01 ∧ u01 = 1) := Or.inl ⟨hcase010a, hcase010b⟩
      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
      ·
        have hcase03 : (s03 = 0 ∧ u03 = 0) ∨ (1 ≤ s03 ∧ u03 = 1) := Or.inl ⟨hcase030a, hcase030b⟩
        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
        ·
          have hcase00 : (s00 = 0 ∧ u00 = 0) ∨ (1 ≤ s00 ∧ u00 = 1) := Or.inl ⟨hcase000a, hcase000b⟩
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            have hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1) := Or.inl ⟨hcase040a, hcase040b⟩
            exact symbolic_mask0_integer_shard000 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase030a hcase030b hcase000a hcase000b hcase040a hcase040b
          ·
            have hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1) := Or.inr ⟨hcase041a, hcase041b⟩
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              have hcase14 : (s14 = 0 ∧ u14 = 0) ∨ (1 ≤ s14 ∧ u14 = 1) := Or.inl ⟨hcase140a, hcase140b⟩
              exact symbolic_mask0_integer_shard001 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase030a hcase030b hcase000a hcase000b hcase041a hcase041b hcase140a hcase140b
            ·
              have hcase14 : (s14 = 0 ∧ u14 = 0) ∨ (1 ≤ s14 ∧ u14 = 1) := Or.inr ⟨hcase141a, hcase141b⟩
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                have hcase13 : (s13 = 0 ∧ u13 = 0) ∨ (1 ≤ s13 ∧ u13 = 1) := Or.inl ⟨hcase130a, hcase130b⟩
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  have hcase11 : (s11 = 0 ∧ u11 = 0) ∨ (1 ≤ s11 ∧ u11 = 1) := Or.inl ⟨hcase110a, hcase110b⟩
                  exact symbolic_mask0_integer_shard002 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase030a hcase030b hcase000a hcase000b hcase041a hcase041b hcase141a hcase141b hcase130a hcase130b hcase110a hcase110b
                ·
                  have hcase11 : (s11 = 0 ∧ u11 = 0) ∨ (1 ≤ s11 ∧ u11 = 1) := Or.inr ⟨hcase111a, hcase111b⟩
                  exact symbolic_mask0_integer_shard003 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase030a hcase030b hcase000a hcase000b hcase041a hcase041b hcase141a hcase141b hcase130a hcase130b hcase111a hcase111b
              ·
                have hcase13 : (s13 = 0 ∧ u13 = 0) ∨ (1 ≤ s13 ∧ u13 = 1) := Or.inr ⟨hcase131a, hcase131b⟩
                exact symbolic_mask0_integer_shard004 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase030a hcase030b hcase000a hcase000b hcase041a hcase041b hcase141a hcase141b hcase131a hcase131b
        ·
          have hcase00 : (s00 = 0 ∧ u00 = 0) ∨ (1 ≤ s00 ∧ u00 = 1) := Or.inr ⟨hcase001a, hcase001b⟩
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            have hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1) := Or.inl ⟨hcase040a, hcase040b⟩
            exact symbolic_mask0_integer_shard005 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b
          ·
            have hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1) := Or.inr ⟨hcase041a, hcase041b⟩
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              have hcase33 : (s33 = 0 ∧ u33 = 0) ∨ (1 ≤ s33 ∧ u33 = 1) := Or.inl ⟨hcase330a, hcase330b⟩
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                have hcase43 : (s43 = 0 ∧ u43 = 0) ∨ (1 ≤ s43 ∧ u43 = 1) := Or.inl ⟨hcase430a, hcase430b⟩
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  have hcase42 : (s42 = 0 ∧ u42 = 0) ∨ (1 ≤ s42 ∧ u42 = 1) := Or.inl ⟨hcase420a, hcase420b⟩
                  exact symbolic_mask0_integer_shard006 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase430a hcase430b hcase420a hcase420b
                ·
                  have hcase42 : (s42 = 0 ∧ u42 = 0) ∨ (1 ≤ s42 ∧ u42 = 1) := Or.inr ⟨hcase421a, hcase421b⟩
                  exact symbolic_mask0_integer_shard007 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase430a hcase430b hcase421a hcase421b
              ·
                have hcase43 : (s43 = 0 ∧ u43 = 0) ∨ (1 ≤ s43 ∧ u43 = 1) := Or.inr ⟨hcase431a, hcase431b⟩
                exact symbolic_mask0_integer_shard008 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase431a hcase431b
            ·
              have hcase33 : (s33 = 0 ∧ u33 = 0) ∨ (1 ≤ s33 ∧ u33 = 1) := Or.inr ⟨hcase331a, hcase331b⟩
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                have hcase10 : (s10 = 0 ∧ u10 = 0) ∨ (1 ≤ s10 ∧ u10 = 1) := Or.inl ⟨hcase100a, hcase100b⟩
                exact symbolic_mask0_integer_shard009 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase100a hcase100b
              ·
                have hcase10 : (s10 = 0 ∧ u10 = 0) ∨ (1 ≤ s10 ∧ u10 = 1) := Or.inr ⟨hcase101a, hcase101b⟩
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  have hcase32 : (s32 = 0 ∧ u32 = 0) ∨ (1 ≤ s32 ∧ u32 = 1) := Or.inl ⟨hcase320a, hcase320b⟩
                  exact symbolic_mask0_integer_shard010 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase101a hcase101b hcase320a hcase320b
                ·
                  have hcase32 : (s32 = 0 ∧ u32 = 0) ∨ (1 ≤ s32 ∧ u32 = 1) := Or.inr ⟨hcase321a, hcase321b⟩
                  exact symbolic_mask0_integer_shard011 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase101a hcase101b hcase321a hcase321b
      ·
        have hcase03 : (s03 = 0 ∧ u03 = 0) ∨ (1 ≤ s03 ∧ u03 = 1) := Or.inr ⟨hcase031a, hcase031b⟩
        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
        ·
          have hcase10 : (s10 = 0 ∧ u10 = 0) ∨ (1 ≤ s10 ∧ u10 = 1) := Or.inl ⟨hcase100a, hcase100b⟩
          rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
          ·
            have hcase12 : (s12 = 0 ∧ u12 = 0) ∨ (1 ≤ s12 ∧ u12 = 1) := Or.inl ⟨hcase120a, hcase120b⟩
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              have hcase11 : (s11 = 0 ∧ u11 = 0) ∨ (1 ≤ s11 ∧ u11 = 1) := Or.inl ⟨hcase110a, hcase110b⟩
              exact symbolic_mask0_integer_shard012 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b
            ·
              have hcase11 : (s11 = 0 ∧ u11 = 0) ∨ (1 ≤ s11 ∧ u11 = 1) := Or.inr ⟨hcase111a, hcase111b⟩
              exact symbolic_mask0_integer_shard013 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b
          ·
            have hcase12 : (s12 = 0 ∧ u12 = 0) ∨ (1 ≤ s12 ∧ u12 = 1) := Or.inr ⟨hcase121a, hcase121b⟩
            exact symbolic_mask0_integer_shard014 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase031a hcase031b hcase100a hcase100b hcase121a hcase121b
        ·
          have hcase10 : (s10 = 0 ∧ u10 = 0) ∨ (1 ≤ s10 ∧ u10 = 1) := Or.inr ⟨hcase101a, hcase101b⟩
          rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
          ·
            have hcase00 : (s00 = 0 ∧ u00 = 0) ∨ (1 ≤ s00 ∧ u00 = 1) := Or.inl ⟨hcase000a, hcase000b⟩
            exact symbolic_mask0_integer_shard015 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase031a hcase031b hcase101a hcase101b hcase000a hcase000b
          ·
            have hcase00 : (s00 = 0 ∧ u00 = 0) ∨ (1 ≤ s00 ∧ u00 = 1) := Or.inr ⟨hcase001a, hcase001b⟩
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              have hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1) := Or.inl ⟨hcase040a, hcase040b⟩
              exact symbolic_mask0_integer_shard016 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase031a hcase031b hcase101a hcase101b hcase001a hcase001b hcase040a hcase040b
            ·
              have hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1) := Or.inr ⟨hcase041a, hcase041b⟩
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                have hcase11 : (s11 = 0 ∧ u11 = 0) ∨ (1 ≤ s11 ∧ u11 = 1) := Or.inl ⟨hcase110a, hcase110b⟩
                exact symbolic_mask0_integer_shard017 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase031a hcase031b hcase101a hcase101b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b
              ·
                have hcase11 : (s11 = 0 ∧ u11 = 0) ∨ (1 ≤ s11 ∧ u11 = 1) := Or.inr ⟨hcase111a, hcase111b⟩
                exact symbolic_mask0_integer_shard018 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase010a hcase010b hcase031a hcase031b hcase101a hcase101b hcase001a hcase001b hcase041a hcase041b hcase111a hcase111b
    ·
      have hcase01 : (s01 = 0 ∧ u01 = 0) ∨ (1 ≤ s01 ∧ u01 = 1) := Or.inr ⟨hcase011a, hcase011b⟩
      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
      ·
        have hcase34 : (s34 = 0 ∧ u34 = 0) ∨ (1 ≤ s34 ∧ u34 = 1) := Or.inl ⟨hcase340a, hcase340b⟩
        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
        ·
          have hcase33 : (s33 = 0 ∧ u33 = 0) ∨ (1 ≤ s33 ∧ u33 = 1) := Or.inl ⟨hcase330a, hcase330b⟩
          exact symbolic_mask0_integer_shard019 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase011a hcase011b hcase340a hcase340b hcase330a hcase330b
        ·
          have hcase33 : (s33 = 0 ∧ u33 = 0) ∨ (1 ≤ s33 ∧ u33 = 1) := Or.inr ⟨hcase331a, hcase331b⟩
          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
          ·
            have hcase03 : (s03 = 0 ∧ u03 = 0) ∨ (1 ≤ s03 ∧ u03 = 1) := Or.inl ⟨hcase030a, hcase030b⟩
            exact symbolic_mask0_integer_shard020 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase011a hcase011b hcase340a hcase340b hcase331a hcase331b hcase030a hcase030b
          ·
            have hcase03 : (s03 = 0 ∧ u03 = 0) ∨ (1 ≤ s03 ∧ u03 = 1) := Or.inr ⟨hcase031a, hcase031b⟩
            exact symbolic_mask0_integer_shard021 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase011a hcase011b hcase340a hcase340b hcase331a hcase331b hcase031a hcase031b
      ·
        have hcase34 : (s34 = 0 ∧ u34 = 0) ∨ (1 ≤ s34 ∧ u34 = 1) := Or.inr ⟨hcase341a, hcase341b⟩
        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
        ·
          have hcase00 : (s00 = 0 ∧ u00 = 0) ∨ (1 ≤ s00 ∧ u00 = 1) := Or.inl ⟨hcase000a, hcase000b⟩
          exact symbolic_mask0_integer_shard022 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase011a hcase011b hcase341a hcase341b hcase000a hcase000b
        ·
          have hcase00 : (s00 = 0 ∧ u00 = 0) ∨ (1 ≤ s00 ∧ u00 = 1) := Or.inr ⟨hcase001a, hcase001b⟩
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            have hcase32 : (s32 = 0 ∧ u32 = 0) ∨ (1 ≤ s32 ∧ u32 = 1) := Or.inl ⟨hcase320a, hcase320b⟩
            exact symbolic_mask0_integer_shard023 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase011a hcase011b hcase341a hcase341b hcase001a hcase001b hcase320a hcase320b
          ·
            have hcase32 : (s32 = 0 ∧ u32 = 0) ∨ (1 ≤ s32 ∧ u32 = 1) := Or.inr ⟨hcase321a, hcase321b⟩
            exact symbolic_mask0_integer_shard024 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase020a hcase020b hcase011a hcase011b hcase341a hcase341b hcase001a hcase001b hcase321a hcase321b
  ·
    have hcase02 : (s02 = 0 ∧ u02 = 0) ∨ (1 ≤ s02 ∧ u02 = 1) := Or.inr ⟨hcase021a, hcase021b⟩
    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
    ·
      have hcase01 : (s01 = 0 ∧ u01 = 0) ∨ (1 ≤ s01 ∧ u01 = 1) := Or.inl ⟨hcase010a, hcase010b⟩
      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
      ·
        have hcase00 : (s00 = 0 ∧ u00 = 0) ∨ (1 ≤ s00 ∧ u00 = 1) := Or.inl ⟨hcase000a, hcase000b⟩
        exact symbolic_mask0_integer_shard025 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase021a hcase021b hcase010a hcase010b hcase000a hcase000b
      ·
        have hcase00 : (s00 = 0 ∧ u00 = 0) ∨ (1 ≤ s00 ∧ u00 = 1) := Or.inr ⟨hcase001a, hcase001b⟩
        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
        ·
          have hcase14 : (s14 = 0 ∧ u14 = 0) ∨ (1 ≤ s14 ∧ u14 = 1) := Or.inl ⟨hcase140a, hcase140b⟩
          exact symbolic_mask0_integer_shard026 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase021a hcase021b hcase010a hcase010b hcase001a hcase001b hcase140a hcase140b
        ·
          have hcase14 : (s14 = 0 ∧ u14 = 0) ∨ (1 ≤ s14 ∧ u14 = 1) := Or.inr ⟨hcase141a, hcase141b⟩
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            have hcase30 : (s30 = 0 ∧ u30 = 0) ∨ (1 ≤ s30 ∧ u30 = 1) := Or.inl ⟨hcase300a, hcase300b⟩
            exact symbolic_mask0_integer_shard027 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase021a hcase021b hcase010a hcase010b hcase001a hcase001b hcase141a hcase141b hcase300a hcase300b
          ·
            have hcase30 : (s30 = 0 ∧ u30 = 0) ∨ (1 ≤ s30 ∧ u30 = 1) := Or.inr ⟨hcase301a, hcase301b⟩
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              have hcase10 : (s10 = 0 ∧ u10 = 0) ∨ (1 ≤ s10 ∧ u10 = 1) := Or.inl ⟨hcase100a, hcase100b⟩
              exact symbolic_mask0_integer_shard028 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase021a hcase021b hcase010a hcase010b hcase001a hcase001b hcase141a hcase141b hcase301a hcase301b hcase100a hcase100b
            ·
              have hcase10 : (s10 = 0 ∧ u10 = 0) ∨ (1 ≤ s10 ∧ u10 = 1) := Or.inr ⟨hcase101a, hcase101b⟩
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                have hcase03 : (s03 = 0 ∧ u03 = 0) ∨ (1 ≤ s03 ∧ u03 = 1) := Or.inl ⟨hcase030a, hcase030b⟩
                exact symbolic_mask0_integer_shard029 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase021a hcase021b hcase010a hcase010b hcase001a hcase001b hcase141a hcase141b hcase301a hcase301b hcase101a hcase101b hcase030a hcase030b
              ·
                have hcase03 : (s03 = 0 ∧ u03 = 0) ∨ (1 ≤ s03 ∧ u03 = 1) := Or.inr ⟨hcase031a, hcase031b⟩
                exact symbolic_mask0_integer_shard030 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase021a hcase021b hcase010a hcase010b hcase001a hcase001b hcase141a hcase141b hcase301a hcase301b hcase101a hcase101b hcase031a hcase031b
    ·
      have hcase01 : (s01 = 0 ∧ u01 = 0) ∨ (1 ≤ s01 ∧ u01 = 1) := Or.inr ⟨hcase011a, hcase011b⟩
      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
      ·
        have hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1) := Or.inl ⟨hcase040a, hcase040b⟩
        exact symbolic_mask0_integer_shard031 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase021a hcase021b hcase011a hcase011b hcase040a hcase040b
      ·
        have hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1) := Or.inr ⟨hcase041a, hcase041b⟩
        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
        ·
          have hcase11 : (s11 = 0 ∧ u11 = 0) ∨ (1 ≤ s11 ∧ u11 = 1) := Or.inl ⟨hcase110a, hcase110b⟩
          exact symbolic_mask0_integer_shard032 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase021a hcase021b hcase011a hcase011b hcase041a hcase041b hcase110a hcase110b
        ·
          have hcase11 : (s11 = 0 ∧ u11 = 0) ∨ (1 ≤ s11 ∧ u11 = 1) := Or.inr ⟨hcase111a, hcase111b⟩
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            have hcase13 : (s13 = 0 ∧ u13 = 0) ∨ (1 ≤ s13 ∧ u13 = 1) := Or.inl ⟨hcase130a, hcase130b⟩
            rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
            ·
              have hcase00 : (s00 = 0 ∧ u00 = 0) ∨ (1 ≤ s00 ∧ u00 = 1) := Or.inl ⟨hcase000a, hcase000b⟩
              exact symbolic_mask0_integer_shard033 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase021a hcase021b hcase011a hcase011b hcase041a hcase041b hcase111a hcase111b hcase130a hcase130b hcase000a hcase000b
            ·
              have hcase00 : (s00 = 0 ∧ u00 = 0) ∨ (1 ≤ s00 ∧ u00 = 1) := Or.inr ⟨hcase001a, hcase001b⟩
              exact symbolic_mask0_integer_shard034 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase021a hcase021b hcase011a hcase011b hcase041a hcase041b hcase111a hcase111b hcase130a hcase130b hcase001a hcase001b
          ·
            have hcase13 : (s13 = 0 ∧ u13 = 0) ∨ (1 ≤ s13 ∧ u13 = 1) := Or.inr ⟨hcase131a, hcase131b⟩
            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
            ·
              have hcase12 : (s12 = 0 ∧ u12 = 0) ∨ (1 ≤ s12 ∧ u12 = 1) := Or.inl ⟨hcase120a, hcase120b⟩
              exact symbolic_mask0_integer_shard035 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase021a hcase021b hcase011a hcase011b hcase041a hcase041b hcase111a hcase111b hcase131a hcase131b hcase120a hcase120b
            ·
              have hcase12 : (s12 = 0 ∧ u12 = 0) ∨ (1 ≤ s12 ∧ u12 = 1) := Or.inr ⟨hcase121a, hcase121b⟩
              exact symbolic_mask0_integer_shard036 n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut120 hcut0 hcut148 hcut1 hcut2 hcut3 hcut4 hcut10 hcut14 hcut20 hcut25 hcut29 hcut31 hcut32 hcut33 hcut35 hcut36 hcut37 hcut38 hcut39 hcut43 hcut44 hcut46 hcut47 hcut48 hcut49 hcut51 hcut52 hcut54 hcut55 hcut60 hcut62 hcut64 hcut65 hcut69 hcut72 hcut73 hcut74 hcut76 hcut79 hcut77 hcut78 hcut80 hcut81 hcut82 hcut83 hcut106 hcut84 hcut85 hcut86 hcut88 hcut89 hcut90 hcut91 hcut92 hcut93 hcut94 hcut95 hcut96 hcut107 hcut98 hcut99 hcut100 hcut101 hcut102 hcut103 hcut104 hcut105 hcut108 hcut109 hcut111 hcut112 hcut113 hcut114 hcut131 hcut115 hcut116 hcut117 hcut118 hcut119 hcut121 hcut132 hcut123 hcut124 hcut125 hcut126 hcut140 hcut127 hcut128 hcut129 hcut149 hcut130 hcut133 hcut134 hcut135 hcut136 hcut137 hcut138 hcut139 hcut143 hcut144 hcut142 hcut145 hcut146 hcut151 hcut147 hcut150 hcut152 hcut153 hcut154 hcut155 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44 hcase021a hcase021b hcase011a hcase011b hcase041a hcase041b hcase111a hcase111b hcase131a hcase131b hcase121a hcase121b

#print axioms symbolic_mask0_integer_closure
end Jsp404.SixExactFloorKernel
