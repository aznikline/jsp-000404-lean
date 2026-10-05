import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_mask255_integer_shard001 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut16 : (s33 + s34 + s40 + s41 + u33 + u34 + u40 + u41) + 1 ≤ (n + 1))
    (hcut81 : (s02 + s04 + s33 + u02 + u04 + u33 + 1) + 1 ≤ (n))
    (hcut35 : (s01 + s32 + u01 + u32 + 1) + 1 ≤ (n))
    (hcut92 : (s02 + s04 + s32 + u02 + u04 + u32 + 1) + 1 ≤ (n))
    (hcut51 : (s02 + s03 + s33 + u02 + u03 + u33 + 2) + 1 ≤ (n))
    (hcut82 : (s00 + s04 + s40 + s44 + u00 + u04 + u40 + u44) + 1 ≤ (2 * n))
    (hcut85 : (s42 + u42) + 1 ≤ (s32 + 2))
    (hcut73 : (s00 + s02 + s04 + s40 + s41 + s44 + u00 + u02 + u04 + u40 + u41 + u44) + 1 ≤ (2 * n + 1))
    (hcut55 : (s00 + s01 + s03 + s04 + u00 + u01 + u03 + u04) + 1 ≤ (n + 1))
    (hcut84 : (s12 + s13 + s32 + s40 + s43 + s44 + u12 + u13 + u32 + u40 + u43 + u44) + 1 ≤ (2 * n))
    (hcut9 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut60 : (s03 + s32 + u03 + u32 + 2) + 1 ≤ (n))
    (hcut2 : (s00 + s02 + s03 + s04 + s44 + u00 + u02 + u03 + u04 + u44) + 1 ≤ (n + s34 + 4))
    (hcut100 : (s34 + s40 + s41 + s42 + u34 + u40 + u41 + u42) + 1 ≤ (n))
    (hcut80 : (s30 + s32 + s33 + u30 + u32 + u33) + 1 ≤ (n))
    (hcut5 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 2))
    (hcut36 : (s03 + s04 + u03 + u04 + 2) + 1 ≤ (n))
    (hcut24 : (s30 + s33 + s34 + s41 + u30 + u33 + u34 + u41) + 1 ≤ (n + 1))
    (hcut69 : (s02 + u02) + 1 ≤ (s34 + 1))
    (hcut94 : (s33 + s40 + s41 + s42 + u33 + u40 + u41 + u42) + 1 ≤ (n))
    (hcut77 : (s02 + s03 + s10 + u02 + u03 + u10 + 2) + 1 ≤ (n))
    (hcut76 : (s03 + s30 + s31 + s32 + u03 + u30 + u31 + u32 + 1) + 1 ≤ (n))
    (hcut65 : (s02 + s03 + s11 + u02 + u03 + u11 + 2) + 1 ≤ (n))
    (hcut4 : (s02 + s03 + s10 + s14 + s32 + s33 + u02 + u03 + u10 + u14 + u32 + u33) + 1 ≤ (n + 1))
    (hcut101 : (s40 + s41 + s42 + s43 + s44 + u40 + u41 + u42 + u43 + u44) + 1 ≤ (n + 1))
    (hcut88 : (s02 + s03 + s41 + s42 + u02 + u03 + u41 + u42 + 2) + 1 ≤ (n))
    (hcut78 : (s30 + s31 + u30 + u31) + 1 ≤ (s10 + 2))
    (hcut23 : (s31 + u31) + 1 ≤ (s10 + 1))
    (hcut53 : (s01 + s43 + u01 + u43) + 1 ≤ (s33 + 2))
    (hcut18 : (s02 + s30 + s31 + s33 + u02 + u30 + u31 + u33 + 1) + 1 ≤ (n))
    (hu00b : u00 ≤ 1)
    (hu00c : u00 ≤ s00)
    (hu01b : u01 ≤ 1)
    (hu01c : u01 ≤ s01)
    (hu02b : u02 ≤ 1)
    (hu02c : u02 ≤ s02)
    (hu03b : u03 ≤ 1)
    (hu03c : u03 ≤ s03)
    (hu04b : u04 ≤ 1)
    (hu04c : u04 ≤ s04)
    (hu10b : u10 ≤ 1)
    (hu10c : u10 ≤ s10)
    (hu11b : u11 ≤ 1)
    (hu11c : u11 ≤ s11)
    (hu12b : u12 ≤ 1)
    (hu12c : u12 ≤ s12)
    (hu13b : u13 ≤ 1)
    (hu13c : u13 ≤ s13)
    (hu14b : u14 ≤ 1)
    (hu14c : u14 ≤ s14)
    (hu30b : u30 ≤ 1)
    (hu30c : u30 ≤ s30)
    (hu31b : u31 ≤ 1)
    (hu31c : u31 ≤ s31)
    (hu32b : u32 ≤ 1)
    (hu32c : u32 ≤ s32)
    (hu33b : u33 ≤ 1)
    (hu33c : u33 ≤ s33)
    (hu34b : u34 ≤ 1)
    (hu34c : u34 ≤ s34)
    (hu40b : u40 ≤ 1)
    (hu40c : u40 ≤ s40)
    (hu41b : u41 ≤ 1)
    (hu41c : u41 ≤ s41)
    (hu42b : u42 ≤ 1)
    (hu42c : u42 ≤ s42)
    (hu43b : u43 ≤ 1)
    (hu43c : u43 ≤ s43)
    (hu44b : u44 ≤ 1)
    (hu44c : u44 ≤ s44)
    (hcase00 : (s00 = 0 ∧ u00 = 0) ∨ (1 ≤ s00 ∧ u00 = 1))
    (hcase01 : (s01 = 0 ∧ u01 = 0) ∨ (1 ≤ s01 ∧ u01 = 1))
    (hcase02 : (s02 = 0 ∧ u02 = 0) ∨ (1 ≤ s02 ∧ u02 = 1))
    (hcase03 : (s03 = 0 ∧ u03 = 0) ∨ (1 ≤ s03 ∧ u03 = 1))
    (hcase04 : (s04 = 0 ∧ u04 = 0) ∨ (1 ≤ s04 ∧ u04 = 1))
    (hcase10 : (s10 = 0 ∧ u10 = 0) ∨ (1 ≤ s10 ∧ u10 = 1))
    (hcase11 : (s11 = 0 ∧ u11 = 0) ∨ (1 ≤ s11 ∧ u11 = 1))
    (hcase12 : (s12 = 0 ∧ u12 = 0) ∨ (1 ≤ s12 ∧ u12 = 1))
    (hcase13 : (s13 = 0 ∧ u13 = 0) ∨ (1 ≤ s13 ∧ u13 = 1))
    (hcase14 : (s14 = 0 ∧ u14 = 0) ∨ (1 ≤ s14 ∧ u14 = 1))
    (hcase30 : (s30 = 0 ∧ u30 = 0) ∨ (1 ≤ s30 ∧ u30 = 1))
    (hcase31 : (s31 = 0 ∧ u31 = 0) ∨ (1 ≤ s31 ∧ u31 = 1))
    (hcase32 : (s32 = 0 ∧ u32 = 0) ∨ (1 ≤ s32 ∧ u32 = 1))
    (hcase33 : (s33 = 0 ∧ u33 = 0) ∨ (1 ≤ s33 ∧ u33 = 1))
    (hcase34 : (s34 = 0 ∧ u34 = 0) ∨ (1 ≤ s34 ∧ u34 = 1))
    (hcase40 : (s40 = 0 ∧ u40 = 0) ∨ (1 ≤ s40 ∧ u40 = 1))
    (hcase41 : (s41 = 0 ∧ u41 = 0) ∨ (1 ≤ s41 ∧ u41 = 1))
    (hcase42 : (s42 = 0 ∧ u42 = 0) ∨ (1 ≤ s42 ∧ u42 = 1))
    (hcase43 : (s43 = 0 ∧ u43 = 0) ∨ (1 ≤ s43 ∧ u43 = 1))
    (hcase44 : (s44 = 0 ∧ u44 = 0) ∨ (1 ≤ s44 ∧ u44 = 1))
    (hcase001a : 1 ≤ s00)
    (hcase001b : u00 = 1)
    (hcase300a : s30 = 0)
    (hcase300b : u30 = 0)
    (hcase330a : s33 = 0)
    (hcase330b : u33 = 0)
    : False := by
  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
  ·
    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
    ·
      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
      ·
        clear hsum_nat0 hsum_nat1 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase340b hcase100b hcase320b hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase340b hcase100b hcase321a hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
    ·
      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
      ·
        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase340b hcase310b hcase320b hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase340b hcase101a hcase101b hcase310b hcase321a hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase340b hcase101a hcase311a hcase320b hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase340b hcase101a hcase101b hcase311a hcase321a hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
  ·
    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
    ·
      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
      ·
        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
        ·
          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase310a hcase310b hcase440b hcase400b hcase410b hcase420b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase43
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320b hcase310a hcase310b hcase440a hcase440b hcase400a hcase400b hcase410a hcase410b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase43
                  omega
              ·
                clear hsum_nat0 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase341a hcase010a hcase010b hcase320b hcase310b hcase440b hcase400a hcase400b hcase411a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase42 hcase43
                omega
            ·
              clear hsum_nat0 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase341a hcase010a hcase010b hcase320b hcase310b hcase440b hcase401a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase41 hcase42 hcase43
              omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                      ·
                        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                        ·
                          clear hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase320a hcase320b hcase310a hcase310b hcase441a hcase400b hcase410b hcase420b hcase430b hcase040b hcase020b hcase030b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase320a hcase320b hcase310a hcase310b hcase441a hcase400b hcase410b hcase420b hcase430b hcase040b hcase020a hcase020b hcase031a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33
                          omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase320a hcase320b hcase310a hcase310b hcase441a hcase400b hcase410b hcase420b hcase430b hcase040b hcase021a hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33
                        omega
                    ·
                      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                      ·
                        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase320a hcase320b hcase310a hcase310b hcase441a hcase400b hcase410b hcase420b hcase430b hcase041a hcase030a hcase030b hcase020b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase320a hcase320b hcase310a hcase310b hcase441a hcase400b hcase410b hcase420b hcase430b hcase041a hcase030b hcase021a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33
                          omega
                      ·
                        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase320a hcase320b hcase310a hcase310b hcase441a hcase400b hcase410b hcase420b hcase430b hcase041a hcase031a hcase020b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase320a hcase320b hcase310a hcase310b hcase441a hcase400b hcase410b hcase420b hcase430b hcase041a hcase031a hcase021a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33
                          omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase310a hcase310b hcase441a hcase441b hcase400a hcase400b hcase410a hcase410b hcase420a hcase420b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320b hcase310a hcase310b hcase441a hcase441b hcase400a hcase400b hcase410a hcase410b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase43
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase341a hcase010a hcase010b hcase320b hcase310b hcase441a hcase441b hcase400a hcase400b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase42 hcase43
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase341a hcase010a hcase010b hcase320b hcase310b hcase441a hcase441b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase41 hcase42 hcase43
              omega
        ·
          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase100b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase101a hcase400b hcase410b hcase420b hcase140a hcase140b hcase040b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase30 hcase33 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase400a hcase400b hcase410a hcase410b hcase420a hcase420b hcase140b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase30 hcase33 hcase43 hcase44
                      omega
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase101a hcase400b hcase410b hcase420b hcase141a hcase141b hcase040b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase30 hcase33 hcase43 hcase44
                      omega
                    ·
                      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                          ·
                            clear hn4 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase320a hcase320b hcase101a hcase101b hcase400b hcase410b hcase420b hcase141a hcase141b hcase041a hcase030b hcase430b hcase020b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase320a hcase320b hcase101a hcase400b hcase410b hcase420b hcase141a hcase041a hcase030a hcase030b hcase430b hcase021a hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase400a hcase400b hcase410a hcase410b hcase420a hcase420b hcase141a hcase141b hcase041a hcase041b hcase030a hcase030b hcase00 hcase02 hcase11 hcase12 hcase13 hcase30 hcase33 hcase44
                          omega
                      ·
                        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase400a hcase400b hcase410a hcase410b hcase420a hcase420b hcase141a hcase141b hcase041a hcase031a hcase020b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase101a hcase400b hcase410b hcase420b hcase141a hcase041a hcase031a hcase021a hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase43 hcase44
                          omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320b hcase311a hcase311b hcase101a hcase101b hcase400a hcase400b hcase410a hcase410b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase43 hcase44
                  omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase320b hcase311a hcase101a hcase400a hcase400b hcase411a hcase420a hcase420b hcase430b hcase020a hcase020b hcase040b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase44
                        omega
                      ·
                        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase400a hcase400b hcase411a hcase420a hcase420b hcase430b hcase020a hcase020b hcase041a hcase041b hcase030a hcase030b hcase440b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33
                            omega
                          ·
                            clear hn4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase320b hcase311a hcase101a hcase101b hcase400a hcase400b hcase411a hcase420a hcase420b hcase430b hcase020b hcase041a hcase030b hcase441a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33
                            omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase400a hcase400b hcase411a hcase411b hcase420a hcase420b hcase430a hcase430b hcase020b hcase041a hcase031a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase44
                          omega
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase320b hcase311a hcase101a hcase400a hcase400b hcase411a hcase420a hcase420b hcase430b hcase021a hcase040b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase44
                        omega
                      ·
                        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase341a hcase010a hcase010b hcase320b hcase311a hcase101a hcase400a hcase400b hcase411a hcase420a hcase420b hcase430b hcase041a hcase041b hcase030a hcase030b hcase440b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase400a hcase400b hcase411a hcase420b hcase430b hcase021a hcase041a hcase030b hcase441a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33
                            omega
                        ·
                          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase400a hcase400b hcase411a hcase411b hcase420a hcase420b hcase430a hcase430b hcase021a hcase021b hcase031a hcase031b hcase140b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase320a hcase320b hcase311a hcase101a hcase400a hcase400b hcase411a hcase420a hcase420b hcase430b hcase021a hcase041a hcase031a hcase141a hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase44
                            omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase400a hcase400b hcase411a hcase411b hcase420a hcase420b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320b hcase311a hcase311b hcase101a hcase101b hcase400a hcase400b hcase411a hcase411b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase43 hcase44
                  omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase320b hcase311a hcase101a hcase401a hcase140a hcase140b hcase040b hcase430b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase401a hcase401b hcase140a hcase140b hcase040a hcase040b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41 hcase42 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase401a hcase401b hcase140b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase320b hcase311a hcase101a hcase401a hcase141a hcase141b hcase040b hcase430b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase401a hcase401b hcase141a hcase141b hcase040a hcase040b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41 hcase42 hcase44
                    omega
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase341a hcase010a hcase010b hcase320b hcase311a hcase101a hcase101b hcase401a hcase141a hcase141b hcase030a hcase030b hcase410a hcase410b hcase420a hcase420b hcase430b hcase440b hcase00 hcase02 hcase11 hcase12 hcase13 hcase30 hcase33
                            omega
                          ·
                            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase401a hcase141a hcase141b hcase041a hcase030b hcase410b hcase420b hcase430b hcase441a hcase020b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase401a hcase141a hcase141b hcase041a hcase030b hcase410a hcase410b hcase420b hcase430b hcase441a hcase021a hcase00 hcase11 hcase12 hcase13 hcase30 hcase33
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase401a hcase401b hcase141a hcase141b hcase041a hcase041b hcase030a hcase030b hcase410a hcase410b hcase420a hcase420b hcase00 hcase02 hcase11 hcase12 hcase13 hcase30 hcase33 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320b hcase311a hcase311b hcase101a hcase101b hcase401a hcase401b hcase141a hcase141b hcase041a hcase041b hcase030a hcase030b hcase410a hcase410b hcase00 hcase02 hcase11 hcase12 hcase13 hcase30 hcase33 hcase43 hcase44
                        omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                          ·
                            clear hn4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase320b hcase311a hcase101a hcase101b hcase401a hcase141a hcase141b hcase041a hcase030b hcase411a hcase420a hcase420b hcase430b hcase020b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase401a hcase141a hcase141b hcase041a hcase030b hcase411a hcase420b hcase430b hcase021a hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase401a hcase141a hcase141b hcase041a hcase041b hcase030a hcase030b hcase411a hcase420a hcase420b hcase431a hcase00 hcase02 hcase11 hcase12 hcase13 hcase30 hcase33 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase401a hcase141a hcase141b hcase041a hcase041b hcase030a hcase030b hcase411a hcase421a hcase00 hcase02 hcase11 hcase12 hcase13 hcase30 hcase33 hcase43 hcase44
                        omega
                  ·
                    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase401a hcase401b hcase141a hcase141b hcase041a hcase031a hcase020b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase320a hcase320b hcase311a hcase101a hcase401a hcase141a hcase041a hcase031a hcase021a hcase430b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase320a hcase320b hcase311a hcase311b hcase101a hcase101b hcase401a hcase401b hcase141a hcase141b hcase041a hcase041b hcase031a hcase031b hcase021a hcase021b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41 hcase42 hcase44
                        omega
      ·
        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
        ·
          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
          ·
            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase030a hcase030b hcase420a hcase420b hcase430b hcase140a hcase140b hcase410a hcase410b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase40
                      omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase020a hcase020b hcase030b hcase420b hcase430b hcase140a hcase140b hcase410b hcase441a hcase400b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33
                        omega
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase010b hcase321a hcase321b hcase020b hcase030b hcase420a hcase420b hcase430b hcase140a hcase140b hcase410a hcase410b hcase441a hcase401a hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase020b hcase030b hcase420b hcase430b hcase140a hcase140b hcase410b hcase441a hcase401a hcase041a hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33
                          omega
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase030a hcase030b hcase420a hcase420b hcase430b hcase140a hcase140b hcase411a hcase040a hcase040b hcase440b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase40
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase010b hcase321a hcase321b hcase020b hcase030b hcase420a hcase420b hcase430b hcase140a hcase140b hcase411a hcase040b hcase441a hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase40
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase030a hcase030b hcase420a hcase420b hcase430a hcase430b hcase140b hcase411a hcase411b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase40 hcase44
                      omega
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase030a hcase030b hcase420a hcase420b hcase430b hcase141a hcase141b hcase310a hcase310b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33 hcase40 hcase41
                      omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase020a hcase020b hcase030b hcase420b hcase430b hcase141a hcase141b hcase310a hcase310b hcase441a hcase400b hcase410b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33
                          omega
                        ·
                          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase010b hcase321a hcase321b hcase020b hcase030b hcase420a hcase420b hcase430b hcase141a hcase141b hcase310a hcase310b hcase441a hcase400a hcase400b hcase411a hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase020a hcase020b hcase030b hcase420a hcase420b hcase430b hcase141a hcase141b hcase310b hcase441a hcase400a hcase400b hcase411a hcase041a hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33
                            omega
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase010b hcase321a hcase321b hcase020b hcase030b hcase420a hcase420b hcase430b hcase141a hcase141b hcase310a hcase310b hcase441a hcase401a hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase020a hcase020b hcase030b hcase420a hcase420b hcase430b hcase141a hcase141b hcase310b hcase441a hcase401a hcase041a hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41
                          omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase030a hcase030b hcase420a hcase420b hcase430a hcase430b hcase141a hcase141b hcase100b hcase00 hcase04 hcase11 hcase12 hcase13 hcase30 hcase33 hcase40 hcase41 hcase44
                      omega
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase020a hcase020b hcase030a hcase030b hcase420b hcase430b hcase101a hcase040b hcase400b hcase410b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase020a hcase020b hcase030a hcase030b hcase420a hcase420b hcase430b hcase311a hcase101a hcase040b hcase400a hcase400b hcase411a hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase020a hcase020b hcase030a hcase030b hcase420a hcase420b hcase430b hcase311a hcase101a hcase040b hcase401a hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41 hcase44
                          omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330a hcase330b hcase341a hcase010a hcase010b hcase321a hcase020a hcase020b hcase030a hcase030b hcase420a hcase420b hcase430b hcase311a hcase101a hcase041a hcase041b hcase410a hcase410b hcase440b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase40
                            omega
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321b hcase020a hcase020b hcase030a hcase030b hcase420b hcase430b hcase141a hcase141b hcase311b hcase101a hcase101b hcase041a hcase410b hcase441a hcase400b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase020b hcase030b hcase420b hcase430b hcase141a hcase141b hcase311a hcase311b hcase101a hcase101b hcase041a hcase410b hcase441a hcase401a hcase00 hcase11 hcase12 hcase13 hcase30 hcase33
                              omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase030a hcase030b hcase420a hcase420b hcase430b hcase141a hcase141b hcase311a hcase311b hcase101a hcase101b hcase041a hcase041b hcase411a hcase440b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase40
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase020a hcase020b hcase030a hcase030b hcase420a hcase420b hcase430b hcase141a hcase311a hcase101a hcase041a hcase411a hcase441a hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase40
                            omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase030a hcase030b hcase420a hcase420b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase44
                omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase030a hcase030b hcase421a hcase410a hcase410b hcase430b hcase040a hcase040b hcase440b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase010b hcase321a hcase321b hcase020b hcase030b hcase421a hcase410a hcase410b hcase430b hcase040b hcase441a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40
                      omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase341a hcase010a hcase010b hcase321a hcase020a hcase020b hcase030a hcase030b hcase421a hcase410a hcase410b hcase430b hcase310b hcase440b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase020a hcase020b hcase030b hcase421a hcase410a hcase410b hcase430b hcase041a hcase310b hcase441a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40
                        omega
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase030a hcase030b hcase421a hcase421b hcase410a hcase410b hcase430a hcase430b hcase311a hcase311b hcase140b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33 hcase40 hcase44
                        omega
                      ·
                        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase030a hcase030b hcase421a hcase421b hcase410a hcase410b hcase430a hcase430b hcase041a hcase041b hcase141a hcase141b hcase100b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase40 hcase44
                          omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut73 hcut55 hcut84 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase020a hcase020b hcase030a hcase030b hcase421a hcase410b hcase430b hcase041a hcase141a hcase101a hcase400b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase020a hcase020b hcase030a hcase030b hcase421a hcase410a hcase410b hcase430b hcase041a hcase311a hcase141a hcase101a hcase401a hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase44
                            omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase030a hcase030b hcase421a hcase421b hcase410a hcase410b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase44
                  omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase010b hcase321a hcase321b hcase020b hcase030b hcase421a hcase411a hcase430b hcase310a hcase310b hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase020a hcase020b hcase030b hcase421a hcase411a hcase430b hcase310b hcase041a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase44
                      omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase010b hcase321a hcase321b hcase020b hcase030b hcase421a hcase411a hcase430b hcase311a hcase311b hcase140a hcase140b hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33 hcase40 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase030a hcase030b hcase421a hcase421b hcase411a hcase411b hcase430a hcase430b hcase311a hcase311b hcase140b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33 hcase40 hcase44
                        omega
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase030a hcase030b hcase421a hcase421b hcase411a hcase411b hcase430a hcase430b hcase141a hcase141b hcase100b hcase00 hcase04 hcase11 hcase12 hcase13 hcase30 hcase33 hcase40 hcase44
                        omega
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase020a hcase020b hcase030a hcase030b hcase421a hcase411a hcase430b hcase311a hcase101a hcase040b hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase40 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase020a hcase020b hcase030a hcase030b hcase421a hcase411a hcase430b hcase311a hcase141a hcase101a hcase041a hcase00 hcase11 hcase12 hcase13 hcase30 hcase33 hcase40 hcase44
                          omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase030a hcase030b hcase421a hcase411a hcase431a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase44
                  omega
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase020b hcase031a hcase040b hcase410b hcase310a hcase310b hcase430b hcase420b hcase400b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase020b hcase031a hcase040b hcase410a hcase410b hcase310b hcase430b hcase420a hcase420b hcase401a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase020b hcase031a hcase040b hcase410a hcase410b hcase310b hcase430b hcase421a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase410a hcase410b hcase310a hcase310b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase42 hcase44
                    omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase020b hcase031a hcase040b hcase410b hcase400b hcase420b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase020b hcase031a hcase040b hcase410b hcase400b hcase421a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase43 hcase44
                      omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330b hcase341a hcase010b hcase321a hcase020b hcase031a hcase040b hcase410a hcase410b hcase311a hcase401a hcase430b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase410a hcase410b hcase311a hcase311b hcase401a hcase401b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase42 hcase44
                      omega
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase020b hcase031a hcase040b hcase411a hcase310b hcase430b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase411a hcase411b hcase310a hcase310b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase42 hcase44
                    omega
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330b hcase341a hcase010b hcase321a hcase020b hcase031a hcase040b hcase411a hcase311a hcase430b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase411a hcase411b hcase311a hcase311b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase42 hcase44
                    omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase020b hcase031a hcase041a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase040a hcase040b hcase100a hcase100b hcase420a hcase420b hcase430b hcase110a hcase110b hcase410a hcase410b hcase440b hcase00 hcase03 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40
                        omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase021a hcase040b hcase100a hcase100b hcase420b hcase430b hcase110a hcase110b hcase410b hcase441a hcase400b hcase00 hcase03 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33
                          omega
                        ·
                          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                          ·
                            clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase021a hcase040a hcase040b hcase100b hcase420a hcase420b hcase430b hcase110a hcase110b hcase410a hcase410b hcase441a hcase401a hcase030b hcase00 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33
                            omega
                          ·
                            clear hn4 hcut16 hcut81 hcut35 hcut92 hcut82 hcut85 hcut73 hcut55 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase021a hcase040b hcase100b hcase420b hcase430b hcase110b hcase410b hcase441a hcase401a hcase031a hcase00 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33
                            omega
                    ·
                      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase021a hcase040b hcase100a hcase100b hcase420a hcase420b hcase430b hcase110a hcase110b hcase411a hcase030a hcase030b hcase400b hcase00 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase021a hcase040a hcase040b hcase100b hcase420a hcase420b hcase430b hcase110a hcase110b hcase411a hcase030b hcase401a hcase00 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase44
                          omega
                      ·
                        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                        ·
                          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase040a hcase040b hcase100a hcase100b hcase420a hcase420b hcase430a hcase430b hcase110b hcase411a hcase411b hcase120b hcase130b hcase00 hcase14 hcase30 hcase31 hcase33 hcase40 hcase44
                            omega
                          ·
                            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase021a hcase040b hcase100a hcase100b hcase420a hcase420b hcase430b hcase110a hcase110b hcase411a hcase031a hcase120a hcase120b hcase131a hcase131b hcase140a hcase140b hcase400b hcase00 hcase30 hcase31 hcase33 hcase44
                                omega
                              ·
                                clear hn4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase021a hcase040b hcase100b hcase420a hcase420b hcase430b hcase110b hcase411a hcase031a hcase120a hcase120b hcase131a hcase140b hcase401a hcase00 hcase30 hcase31 hcase33 hcase44
                                omega
                            ·
                              clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase021a hcase040b hcase100a hcase100b hcase420a hcase420b hcase430b hcase110a hcase110b hcase411a hcase031a hcase120a hcase120b hcase131a hcase131b hcase00 hcase30 hcase31 hcase33 hcase40 hcase44
                              omega
                        ·
                          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase021a hcase040b hcase100a hcase100b hcase420a hcase420b hcase430b hcase110a hcase110b hcase411a hcase031a hcase121a hcase121b hcase140a hcase140b hcase400b hcase00 hcase13 hcase30 hcase31 hcase33 hcase44
                              omega
                            ·
                              clear hn4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase021a hcase040b hcase100b hcase420a hcase420b hcase430b hcase110b hcase411a hcase031a hcase121a hcase140b hcase401a hcase00 hcase13 hcase30 hcase31 hcase33 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase021a hcase040b hcase100a hcase100b hcase420a hcase420b hcase430b hcase110a hcase110b hcase411a hcase031a hcase121a hcase121b hcase00 hcase13 hcase30 hcase31 hcase33 hcase40 hcase44
                            omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase021a hcase040b hcase100a hcase100b hcase420b hcase430b hcase400b hcase410b hcase00 hcase03 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase021a hcase040b hcase100a hcase100b hcase420a hcase420b hcase430b hcase111a hcase111b hcase400b hcase411a hcase00 hcase03 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase44
                        omega
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                          ·
                            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase040a hcase040b hcase100b hcase420a hcase420b hcase430a hcase430b hcase111a hcase401a hcase401b hcase140b hcase410a hcase410b hcase130b hcase120b hcase00 hcase03 hcase30 hcase31 hcase33 hcase44
                              omega
                            ·
                              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                              ·
                                clear hn4 hsum_nat0 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330a hcase330b hcase341a hcase010a hcase010b hcase321a hcase040a hcase040b hcase100b hcase420b hcase430b hcase111a hcase401a hcase140b hcase410b hcase130a hcase130b hcase121a hcase440b hcase00 hcase03 hcase30 hcase31 hcase33
                                omega
                              ·
                                clear hn4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase021a hcase040b hcase100b hcase420b hcase430b hcase111a hcase401a hcase140b hcase410b hcase130a hcase130b hcase121a hcase441a hcase00 hcase03 hcase30 hcase31 hcase33
                                omega
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase040a hcase040b hcase100a hcase100b hcase420a hcase420b hcase430b hcase111a hcase111b hcase401a hcase140a hcase140b hcase410a hcase410b hcase131a hcase131b hcase440b hcase00 hcase03 hcase12 hcase30 hcase31 hcase33
                              omega
                            ·
                              clear hn4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase021a hcase040b hcase100b hcase420b hcase430b hcase111a hcase401a hcase140b hcase410b hcase131a hcase441a hcase00 hcase03 hcase12 hcase30 hcase31 hcase33
                              omega
                        ·
                          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                          ·
                            clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase021a hcase040a hcase040b hcase100b hcase420a hcase420b hcase430b hcase111a hcase111b hcase401a hcase140a hcase140b hcase411a hcase030b hcase00 hcase12 hcase13 hcase30 hcase31 hcase33 hcase44
                            omega
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase021a hcase040a hcase040b hcase100b hcase420a hcase420b hcase430b hcase111a hcase111b hcase401a hcase140a hcase140b hcase411a hcase031a hcase440b hcase00 hcase12 hcase13 hcase30 hcase31 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase321b hcase021a hcase040a hcase040b hcase100a hcase100b hcase420a hcase420b hcase430b hcase111a hcase111b hcase401a hcase140a hcase140b hcase411a hcase031a hcase441a hcase00 hcase12 hcase13 hcase30 hcase31 hcase33
                              omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase341a hcase010a hcase010b hcase321a hcase040a hcase040b hcase100b hcase420a hcase420b hcase430b hcase111a hcase111b hcase401a hcase141a hcase141b hcase440b hcase00 hcase03 hcase12 hcase13 hcase30 hcase31 hcase33 hcase41
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase021a hcase040b hcase100a hcase100b hcase420a hcase420b hcase430b hcase111a hcase111b hcase401a hcase441a hcase00 hcase03 hcase12 hcase13 hcase30 hcase31 hcase33 hcase41
                          omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase040a hcase040b hcase100a hcase100b hcase420a hcase420b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase44
                  omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase021a hcase040b hcase100a hcase100b hcase421a hcase430b hcase030a hcase030b hcase400b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase41 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase021a hcase040a hcase040b hcase100b hcase421a hcase430b hcase030b hcase401a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase41 hcase44
                      omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase021a hcase040b hcase100a hcase100b hcase421a hcase430b hcase031a hcase400b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase41 hcase44
                      omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase341a hcase010a hcase010b hcase321a hcase021a hcase021b hcase040a hcase040b hcase100b hcase421a hcase430b hcase401a hcase440b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase41
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase321b hcase021a hcase040a hcase040b hcase100a hcase100b hcase421a hcase430b hcase031a hcase401a hcase441a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase41
                        omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase040a hcase040b hcase100a hcase100b hcase421a hcase421b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase44
                  omega
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase040b hcase310a hcase310b hcase030a hcase030b hcase410b hcase400b hcase420b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase43 hcase44
                        omega
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase021a hcase040b hcase101a hcase101b hcase310a hcase310b hcase030a hcase030b hcase410a hcase410b hcase400b hcase421a hcase430b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase040a hcase040b hcase101a hcase101b hcase310a hcase310b hcase030a hcase030b hcase410a hcase410b hcase400a hcase400b hcase421a hcase421b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase44
                          omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase040a hcase040b hcase101a hcase101b hcase310a hcase310b hcase030a hcase030b hcase410a hcase410b hcase401a hcase430b hcase440b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase42
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase021a hcase040a hcase040b hcase101a hcase101b hcase310b hcase030b hcase410a hcase410b hcase401a hcase430b hcase441a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase42
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase040a hcase040b hcase101a hcase101b hcase310a hcase310b hcase030a hcase030b hcase410a hcase410b hcase401a hcase401b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase42 hcase44
                        omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase021a hcase040b hcase101a hcase101b hcase310a hcase310b hcase030a hcase030b hcase411a hcase430b hcase400b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase021a hcase040a hcase040b hcase101a hcase101b hcase310b hcase030b hcase411a hcase430b hcase401a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase42 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase040a hcase040b hcase101a hcase101b hcase310a hcase310b hcase030a hcase030b hcase411a hcase411b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase42 hcase44
                      omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase021a hcase040b hcase310a hcase310b hcase031a hcase410b hcase420b hcase430b hcase400b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase021a hcase040b hcase310b hcase031a hcase410a hcase410b hcase420a hcase420b hcase430b hcase401a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase040a hcase040b hcase101a hcase101b hcase310a hcase310b hcase031a hcase031b hcase410a hcase410b hcase420a hcase420b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase44
                        omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase040b hcase101a hcase101b hcase310a hcase310b hcase031a hcase410a hcase410b hcase421a hcase400b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010a hcase010b hcase321a hcase021a hcase040b hcase310b hcase031a hcase410a hcase410b hcase421a hcase401a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase43 hcase44
                        omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase040b hcase101a hcase101b hcase310a hcase310b hcase031a hcase411a hcase400b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010a hcase010b hcase321a hcase021a hcase040b hcase310b hcase031a hcase411a hcase401a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase42 hcase43 hcase44
                      omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase040b hcase101a hcase400b hcase410b hcase420b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase43 hcase44
                      omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase021a hcase040b hcase101a hcase400b hcase410b hcase421a hcase430b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase040a hcase040b hcase101a hcase101b hcase311a hcase311b hcase400a hcase400b hcase410a hcase410b hcase421a hcase421b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase44
                        omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase021a hcase040b hcase101a hcase101b hcase311a hcase311b hcase400b hcase411a hcase430b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase040b hcase101a hcase101b hcase311a hcase311b hcase400b hcase411a hcase431a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase42 hcase44
                      omega
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase040a hcase040b hcase101a hcase101b hcase311a hcase311b hcase401a hcase430b hcase440b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase41 hcase42
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase021a hcase040b hcase101a hcase311a hcase401a hcase430b hcase441a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase41 hcase42
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase040a hcase040b hcase101a hcase101b hcase311a hcase311b hcase401a hcase401b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase41 hcase42 hcase44
                    omega
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase140b hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase021a hcase041a hcase141a hcase141b hcase400b hcase410b hcase420b hcase430b hcase030b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase021a hcase041a hcase141a hcase400b hcase410b hcase420b hcase430b hcase031a hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase041a hcase041b hcase141a hcase141b hcase400a hcase400b hcase410a hcase410b hcase420a hcase420b hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase44
                      omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase041a hcase041b hcase141a hcase141b hcase400b hcase410a hcase410b hcase421a hcase430b hcase440b hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33
                        omega
                      ·
                        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut51 hcut82 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase021a hcase041a hcase141a hcase141b hcase400b hcase410b hcase421a hcase430b hcase441a hcase030b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut73 hcut55 hcut84 hcut9 hcut60 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010b hcase321a hcase321b hcase021a hcase041a hcase141a hcase141b hcase400b hcase410b hcase421a hcase430b hcase441a hcase031a hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase041a hcase041b hcase141a hcase141b hcase400a hcase400b hcase410a hcase410b hcase421a hcase421b hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase44
                      omega
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase341a hcase010a hcase010b hcase321a hcase141a hcase141b hcase400a hcase400b hcase411a hcase430b hcase310b hcase440b hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33 hcase42
                        omega
                      ·
                        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                        ·
                          clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase021a hcase041a hcase141a hcase141b hcase400a hcase400b hcase411a hcase430b hcase310b hcase441a hcase030b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33 hcase42
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase321b hcase021a hcase041a hcase141a hcase141b hcase400a hcase400b hcase411a hcase430b hcase310a hcase310b hcase441a hcase031a hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33 hcase42
                          omega
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase041a hcase041b hcase141a hcase141b hcase400a hcase400b hcase411a hcase411b hcase430a hcase430b hcase100b hcase00 hcase03 hcase11 hcase12 hcase13 hcase30 hcase33 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase021a hcase041a hcase141a hcase400a hcase400b hcase411a hcase430b hcase311a hcase101a hcase00 hcase03 hcase11 hcase12 hcase13 hcase30 hcase33 hcase42 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase041a hcase041b hcase141a hcase141b hcase400a hcase400b hcase411a hcase411b hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase42 hcase44
                    omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                    ·
                      clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330b hcase341a hcase010b hcase321a hcase021a hcase041a hcase141a hcase141b hcase401a hcase430b hcase310b hcase030b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41 hcase42 hcase44
                      omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut16 hcut81 hcut35 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300b hcase330b hcase341a hcase010a hcase010b hcase321a hcase141a hcase141b hcase401a hcase430b hcase310b hcase031a hcase031b hcase440b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase321b hcase021a hcase041a hcase141a hcase141b hcase401a hcase430b hcase310a hcase310b hcase031a hcase441a hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41 hcase42
                        omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase041a hcase041b hcase141a hcase141b hcase401a hcase401b hcase430a hcase430b hcase100b hcase00 hcase03 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut60 hcut2 hcut80 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut101 hcut88 hcut78 hcut53 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase300b hcase330a hcase330b hcase341a hcase010b hcase321a hcase021a hcase041a hcase141a hcase401a hcase430b hcase311a hcase101a hcase00 hcase03 hcase11 hcase12 hcase13 hcase30 hcase33 hcase41 hcase42 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase010a hcase010b hcase321a hcase321b hcase021a hcase021b hcase041a hcase041b hcase141a hcase141b hcase401a hcase401b hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase41 hcase42 hcase44
                  omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut16 hcut81 hcut35 hcut92 hcut51 hcut82 hcut85 hcut73 hcut55 hcut84 hcut9 hcut60 hcut2 hcut100 hcut80 hcut5 hcut36 hcut24 hcut69 hcut94 hcut77 hcut76 hcut65 hcut4 hcut101 hcut88 hcut78 hcut23 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase300a hcase300b hcase330b hcase341a hcase341b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
      omega

#print axioms symbolic_mask255_integer_shard001
end Jsp404.SixExactFloorKernel
