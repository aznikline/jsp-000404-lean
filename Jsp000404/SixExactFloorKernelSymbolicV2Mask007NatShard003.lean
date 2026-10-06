import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask7_integer_shard003 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut66 : (s00 + s04 + s32 + s40 + s44 + u00 + u04 + u32 + u40 + u44) + 1 ≤ (2 * n))
    (hcut51 : (s00 + s01 + u00 + u01) + 1 ≤ (n))
    (hcut81 : (s13 + s14 + s40 + u13 + u14 + u40) + 1 ≤ (n + 1))
    (hcut63 : (s00 + s04 + s33 + s40 + s44 + u00 + u04 + u33 + u40 + u44) + 1 ≤ (2 * n))
    (hcut69 : (s01 + s14 + s33 + s40 + s41 + u01 + u14 + u33 + u40 + u41) + 1 ≤ (2 * n))
    (hcut60 : (s00 + s01 + s32 + s33 + s44 + u00 + u01 + u32 + u33 + u44) + 1 ≤ (n + 2))
    (hcut74 : (s12 + s13 + s14 + s30 + u12 + u13 + u14 + u30) + 1 ≤ (n + 1))
    (hcut50 : (s01 + s02 + s43 + u01 + u02 + u43) + 1 ≤ (n))
    (hcut68 : (s01 + s40 + u01 + u40 + 3) + 1 ≤ (2 * n))
    (hcut82 : (s00 + s01 + s04 + s40 + s44 + u00 + u01 + u04 + u40 + u44) + 1 ≤ (2 * n))
    (hcut55 : (s00 + s01 + s02 + s34 + s42 + u00 + u01 + u02 + u34 + u42) + 1 ≤ (n + 2))
    (hcut76 : (s00 + s01 + s04 + s13 + s33 + s40 + u00 + u01 + u04 + u13 + u33 + u40) + 1 ≤ (2 * n + 1))
    (hcut67 : (s00 + s04 + s32 + s33 + s40 + u00 + u04 + u32 + u33 + u40) + 1 ≤ (2 * n))
    (hcut56 : (s02 + s04 + u02 + u04) + 1 ≤ (n))
    (hcut49 : (s00 + s04 + s30 + s42 + s44 + u00 + u04 + u30 + u42 + u44) + 1 ≤ (2 * n + 2))
    (hcut0 : (s02 + s30 + s31 + s34 + s42 + s43 + u02 + u30 + u31 + u34 + u42 + u43) + 1 ≤ (n + 1))
    (hcut48 : (s01 + s42 + s43 + u01 + u42 + u43) + 1 ≤ (n))
    (hcut17 : (s02 + s11 + s31 + u02 + u11 + u31 + 1) + 1 ≤ (n))
    (hcut12 : (s11 + s31 + s42 + u11 + u31 + u42) + 1 ≤ (n))
    (hcut47 : (s43 + u43) + 1 ≤ (s33 + 2))
    (hcut15 : (s00 + s40 + u00 + u40 + 2) + 1 ≤ (2 * n))
    (hcut46 : (s01 + s32 + s33 + s44 + u01 + u32 + u33 + u44) + 1 ≤ (n + 1))
    (hcut13 : (s40 + s42 + u40 + u42) + 1 ≤ (n))
    (hcut10 : (s13 + s40 + u13 + u40) + 1 ≤ (n))
    (hcut41 : (s13 + s30 + u13 + u30) + 1 ≤ (n))
    (hcut6 : (s00 + s33 + u00 + u33) + 1 ≤ (n))
    (hcut39 : (s02 + s03 + u02 + u03 + 1) + 1 ≤ (n))
    (hcut5 : (s00 + s32 + u00 + u32) + 1 ≤ (n))
    (hcut38 : (s00 + s43 + s44 + u00 + u43 + u44) + 1 ≤ (n + 1))
    (hcut2 : (s03 + s41 + u03 + u41) + 1 ≤ (s13 + 2))
    (hcut37 : (s32 + s44 + u32 + u44) + 1 ≤ (n))
    (hcut36 : (s33 + s44 + u33 + u44) + 1 ≤ (n))
    (hcut1 : (s00 + s04 + s13 + s32 + s33 + s40 + s44 + u00 + u04 + u13 + u32 + u33 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut35 : (s02 + s03 + s14 + s30 + u02 + u03 + u14 + u30) + 1 ≤ (n + 1))
    (hcut34 : (s00 + s02 + s34 + u00 + u02 + u34) + 1 ≤ (n + 2))
    (hcut33 : (s00 + s02 + s42 + u00 + u02 + u42) + 1 ≤ (n + 1))
    (hcut32 : (s00 + s02 + s14 + u00 + u02 + u14) + 1 ≤ (n + 2))
    (hcut30 : (s00 + s02 + s43 + u00 + u02 + u43) + 1 ≤ (n + 1))
    (hcut29 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut26 : (s00 + s32 + s33 + s40 + u00 + u32 + u33 + u40) + 1 ≤ (2 * n))
    (hcut23 : (s10 + s11 + s31 + s32 + s33 + s40 + u10 + u11 + u31 + u32 + u33 + u40 + 1) + 1 ≤ (2 * n))
    (hcut25 : (s00 + s32 + s33 + s44 + u00 + u32 + u33 + u44) + 1 ≤ (n + 2))
    (hcut20 : (s14 + s40 + u14 + u40) + 1 ≤ (n + 1))
    (hcut19 : (s02 + s10 + s11 + u02 + u10 + u11) + 1 ≤ (n))
    (hcut18 : (s12 + s30 + u12 + u30 + 1) + 1 ≤ (n))
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
    (hmincount0 : u00 + (u01 + (u02 + (u03 + (u04)))) ≤ 2)
    (hmincount1 : u10 + (u11 + (u12 + (u13 + (u14)))) ≤ 3)
    (hmincount3 : u30 + (u31 + (u32 + (u33 + (u34)))) ≤ 3)
    (hmincount4 : u40 + (u41 + (u42 + (u43 + (u44)))) ≤ 2)
    (hminend0 : u01 + (u02 + (u03 + (u04))) ≤ 1)
    (hminend4 : u40 + (u41 + (u42 + (u43))) ≤ 1)
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
    (hcase031a : 1 ≤ s03)
    (hcase031b : u03 = 1)
    : False := by
  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
  ·
    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
    ·
      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
      ·
        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase130b hcase00 hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hsum_nat0 hsum_nat1 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300b hcase320b hcase330b hcase131a hcase131b hcase340b hcase310b hcase00 hcase03 hcase10 hcase11 hcase12 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase131a hcase131b hcase340a hcase340b hcase311a hcase311b hcase400b hcase420b hcase430b hcase440b hcase00 hcase03 hcase10 hcase11 hcase12 hcase14 hcase41
                            omega
                          ·
                            rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                            ·
                              clear hn4 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase131a hcase131b hcase340a hcase340b hcase311a hcase311b hcase400a hcase400b hcase420a hcase420b hcase430a hcase430b hcase441a hcase441b hcase000b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41
                              omega
                            ·
                              clear hn4 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase131a hcase131b hcase340a hcase340b hcase311a hcase311b hcase400b hcase420b hcase430a hcase430b hcase441a hcase001a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase330b hcase131a hcase131b hcase340a hcase340b hcase311a hcase311b hcase400a hcase400b hcase420a hcase420b hcase00 hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300b hcase320b hcase330b hcase131a hcase131b hcase340b hcase311a hcase400a hcase400b hcase00 hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase43 hcase44
                        omega
                    ·
                      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase131a hcase340a hcase340b hcase311a hcase311b hcase000b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase131a hcase340a hcase340b hcase311a hcase311b hcase401a hcase001a hcase001b hcase420b hcase430b hcase440b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase131a hcase340a hcase340b hcase311a hcase311b hcase401a hcase001a hcase420b hcase430a hcase430b hcase441a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase131a hcase131b hcase340a hcase340b hcase311a hcase311b hcase401a hcase001a hcase001b hcase420a hcase420b hcase431a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase131a hcase131b hcase340a hcase340b hcase311a hcase311b hcase401a hcase001a hcase001b hcase421a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase43 hcase44
                          omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase330b hcase131a hcase131b hcase341a hcase341b hcase420b hcase440b hcase400b hcase00 hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase41 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase330b hcase131a hcase341a hcase341b hcase420b hcase440b hcase401a hcase00 hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase41 hcase43
                        omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                        ·
                          clear hn4 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase131a hcase131b hcase341a hcase341b hcase420a hcase420b hcase441a hcase441b hcase400a hcase400b hcase000b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase41 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase131a hcase131b hcase341a hcase341b hcase420b hcase441a hcase400b hcase001a hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase41 hcase43
                          omega
                      ·
                        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase131a hcase341a hcase341b hcase420a hcase420b hcase441a hcase441b hcase000b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase41 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase131a hcase341a hcase341b hcase420b hcase441a hcase401a hcase001a hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase41 hcase43
                          omega
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase131a hcase131b hcase341a hcase341b hcase421a hcase421b hcase000b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase40 hcase41 hcase43 hcase44
                      omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300b hcase320b hcase330b hcase131a hcase131b hcase341a hcase310b hcase03 hcase10 hcase11 hcase12 hcase14 hcase40 hcase41 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320b hcase330b hcase131a hcase131b hcase341a hcase001a hcase001b hcase311a hcase03 hcase10 hcase11 hcase12 hcase14 hcase40 hcase41 hcase43 hcase44
                        omega
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase331a hcase331b hcase430a hcase430b hcase440a hcase440b hcase130b hcase00 hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase40 hcase41 hcase42
                    omega
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010b hcase300a hcase300b hcase320a hcase320b hcase331a hcase331b hcase430a hcase430b hcase440a hcase440b hcase131a hcase131b hcase000b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase40 hcase41 hcase42
                      omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300b hcase320b hcase331a hcase430a hcase430b hcase440a hcase440b hcase131a hcase131b hcase340b hcase310b hcase03 hcase10 hcase11 hcase12 hcase14 hcase40 hcase41 hcase42
                          omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300b hcase320b hcase331a hcase430b hcase440b hcase131a hcase131b hcase001a hcase340b hcase311a hcase400b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase42
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut47 hcut15 hcut46 hcut13 hcut41 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300b hcase320b hcase331a hcase430b hcase440b hcase131a hcase001a hcase340b hcase311a hcase401a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase42
                            omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase331a hcase331b hcase430b hcase440b hcase131a hcase131b hcase001a hcase400b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase41 hcase42
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase331a hcase331b hcase430b hcase440b hcase131a hcase001a hcase401a hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase41 hcase42
                          omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase331a hcase331b hcase430a hcase430b hcase441a hcase441b hcase130b hcase00 hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase40 hcase41 hcase42
                    omega
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase320a hcase320b hcase331a hcase331b hcase430a hcase430b hcase441a hcase441b hcase131a hcase131b hcase000b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase40 hcase41 hcase42
                      omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300b hcase320b hcase331a hcase430a hcase430b hcase131a hcase131b hcase001a hcase001b hcase400a hcase400b hcase340b hcase310b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase42
                            omega
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              clear hn4 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase430b hcase441a hcase131a hcase131b hcase001a hcase400b hcase340a hcase340b hcase311a hcase311b hcase420b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41
                              omega
                            ·
                              clear hn4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase300b hcase320a hcase320b hcase331a hcase430b hcase441a hcase131a hcase131b hcase001a hcase400b hcase340b hcase311a hcase421a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41
                              omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                            ·
                              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase430b hcase441a hcase131a hcase131b hcase400b hcase341a hcase341b hcase410b hcase310a hcase310b hcase420b hcase03 hcase10 hcase11 hcase12 hcase14
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300b hcase320a hcase320b hcase331a hcase430b hcase441a hcase131a hcase131b hcase400b hcase341a hcase410b hcase310b hcase421a hcase03 hcase10 hcase11 hcase12 hcase14
                                omega
                            ·
                              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase430b hcase441a hcase131a hcase131b hcase400b hcase341a hcase341b hcase410b hcase311a hcase311b hcase420b hcase03 hcase10 hcase11 hcase12 hcase14
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase331a hcase430a hcase430b hcase441a hcase131a hcase131b hcase400b hcase341a hcase410b hcase311a hcase421a hcase03 hcase10 hcase11 hcase12 hcase14
                                omega
                          ·
                            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                            ·
                              clear hn4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase300b hcase320a hcase320b hcase331a hcase430b hcase441a hcase131a hcase131b hcase001a hcase400b hcase341a hcase310b hcase03 hcase10 hcase11 hcase12 hcase14 hcase42
                              omega
                            ·
                              clear hn4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase331a hcase430a hcase430b hcase441a hcase131a hcase131b hcase001a hcase400b hcase341a hcase411a hcase311a hcase03 hcase10 hcase11 hcase12 hcase14 hcase42
                              omega
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase430b hcase441a hcase131a hcase001a hcase401a hcase420b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase41
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase331a hcase331b hcase430a hcase430b hcase441a hcase441b hcase131a hcase131b hcase001a hcase001b hcase401a hcase421a hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase41
                          omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase320a hcase320b hcase331a hcase331b hcase431a hcase431b hcase420a hcase420b hcase400a hcase400b hcase000b hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase41 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase320a hcase320b hcase331a hcase331b hcase431a hcase420b hcase400b hcase001a hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase41 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase331a hcase331b hcase431a hcase420a hcase420b hcase401a hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase41 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase320a hcase320b hcase331a hcase331b hcase431a hcase421a hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase40 hcase41 hcase44
                  omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase321a hcase321b hcase130b hcase00 hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
              ·
                clear hn4 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase321a hcase321b hcase131a hcase131b hcase000b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300b hcase321a hcase131a hcase131b hcase330b hcase400a hcase400b hcase440a hcase440b hcase340b hcase310b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase42 hcase43
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase131a hcase131b hcase001a hcase330b hcase400b hcase440b hcase340a hcase340b hcase311a hcase311b hcase420b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase43
                            omega
                          ·
                            clear hn4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010b hcase300a hcase300b hcase321a hcase131a hcase131b hcase001a hcase330b hcase400b hcase440b hcase340a hcase340b hcase311a hcase421a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase43
                            omega
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          clear hn4 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase300a hcase300b hcase131a hcase131b hcase001a hcase330b hcase400b hcase440b hcase341a hcase341b hcase420b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase41 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase321a hcase321b hcase131a hcase131b hcase001a hcase330b hcase400b hcase440b hcase421a hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase41 hcase43
                          omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          clear hn4 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase300a hcase300b hcase131a hcase131b hcase001a hcase330a hcase330b hcase400b hcase441a hcase430b hcase420b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase41
                          omega
                        ·
                          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                          ·
                            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300b hcase321a hcase131a hcase131b hcase330b hcase400a hcase400b hcase441a hcase441b hcase430a hcase430b hcase421a hcase421b hcase340b hcase310b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41
                              omega
                            ·
                              clear hn4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase300b hcase321a hcase131a hcase131b hcase001a hcase330a hcase330b hcase400b hcase441a hcase430b hcase421a hcase340b hcase311a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41
                              omega
                          ·
                            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                            ·
                              clear hn4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300b hcase321a hcase131a hcase131b hcase330a hcase330b hcase400b hcase441a hcase430b hcase421a hcase341a hcase310b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41
                              omega
                            ·
                              clear hn4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase321a hcase131a hcase131b hcase001a hcase330a hcase330b hcase400b hcase441a hcase430a hcase430b hcase421a hcase341a hcase311a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41
                              omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase321a hcase321b hcase131a hcase131b hcase001a hcase001b hcase330b hcase400a hcase400b hcase441a hcase441b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase41 hcase42
                        omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase300a hcase300b hcase131a hcase001a hcase330a hcase330b hcase401a hcase430b hcase420b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase41 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase321a hcase321b hcase131a hcase131b hcase001a hcase001b hcase330a hcase330b hcase401a hcase430a hcase430b hcase421a hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase41 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase321a hcase321b hcase131a hcase131b hcase001a hcase001b hcase330a hcase330b hcase401a hcase431a hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase41 hcase42 hcase44
                      omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase300a hcase300b hcase131a hcase131b hcase001a hcase331a hcase420b hcase400b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase300a hcase300b hcase131a hcase001a hcase331a hcase420b hcase401a hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase41 hcase43 hcase44
                      omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            clear hn4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300b hcase321a hcase131a hcase131b hcase331a hcase421a hcase430b hcase340b hcase400b hcase310b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase44
                            omega
                          ·
                            clear hn4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase300b hcase321a hcase131a hcase131b hcase001a hcase331a hcase421a hcase430b hcase340b hcase400b hcase311a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase321a hcase321b hcase131a hcase131b hcase001a hcase001b hcase331a hcase331b hcase421a hcase430a hcase430b hcase340a hcase340b hcase401a hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase41 hcase44
                          omega
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300b hcase321a hcase131a hcase131b hcase331a hcase421a hcase430b hcase341a hcase310b hcase400b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase321a hcase321b hcase131a hcase131b hcase001a hcase001b hcase331a hcase331b hcase421a hcase430a hcase430b hcase341a hcase341b hcase310a hcase310b hcase401a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase321a hcase131a hcase131b hcase001a hcase001b hcase331a hcase421a hcase421b hcase430a hcase430b hcase341a hcase311a hcase03 hcase10 hcase11 hcase12 hcase14 hcase40 hcase41 hcase44
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase300a hcase300b hcase321a hcase321b hcase131a hcase131b hcase001a hcase001b hcase331a hcase331b hcase421a hcase431a hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase34 hcase40 hcase41 hcase44
                      omega
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase301b hcase130b hcase00 hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
            ·
              clear hn4 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase301a hcase301b hcase131a hcase131b hcase000b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase131a hcase001a hcase001b hcase330b hcase340b hcase310b hcase320b hcase03 hcase10 hcase11 hcase12 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut6 hcut39 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase301a hcase131a hcase001a hcase330b hcase340b hcase310b hcase321a hcase03 hcase10 hcase11 hcase12 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut6 hcut39 hcut5 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase131a hcase001a hcase330a hcase330b hcase340a hcase340b hcase311a hcase311b hcase400b hcase420b hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase41 hcase43 hcase44
                        omega
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          clear hn4 hsum_nat1 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut6 hcut39 hcut5 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010b hcase131a hcase001a hcase330b hcase340a hcase340b hcase311a hcase400b hcase421a hcase320b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010a hcase010b hcase131a hcase001a hcase330a hcase330b hcase340a hcase340b hcase311a hcase400b hcase421a hcase321a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase43 hcase44
                          omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase131a hcase001a hcase001b hcase330b hcase340a hcase340b hcase311a hcase401a hcase320b hcase440b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase42 hcase43
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase301a hcase301b hcase131a hcase001a hcase330a hcase330b hcase340a hcase340b hcase311a hcase311b hcase401a hcase320a hcase320b hcase441a hcase420b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase131b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase311a hcase311b hcase401a hcase320a hcase320b hcase441a hcase441b hcase421a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase43
                            omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat1 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010b hcase301a hcase131a hcase001a hcase330b hcase340a hcase340b hcase311a hcase401a hcase321a hcase440b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase42 hcase43
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase001a hcase330a hcase330b hcase340a hcase340b hcase311a hcase311b hcase401a hcase441a hcase420b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase131b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase311a hcase311b hcase401a hcase321a hcase321b hcase441a hcase441b hcase421a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase43
                            omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut6 hcut39 hcut5 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase131a hcase001a hcase330a hcase330b hcase341a hcase341b hcase400b hcase420b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase32 hcase41 hcase43 hcase44
                      omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase131a hcase131b hcase001a hcase001b hcase330b hcase341a hcase400a hcase400b hcase320b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase41 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010a hcase010b hcase131a hcase001a hcase330a hcase330b hcase341a hcase400b hcase421a hcase321a hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase41 hcase43 hcase44
                        omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase001a hcase001b hcase330a hcase330b hcase341a hcase341b hcase401a hcase420b hcase430b hcase440b hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase32 hcase41
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase301a hcase301b hcase131a hcase001a hcase330a hcase330b hcase341a hcase341b hcase401a hcase420b hcase430a hcase430b hcase441a hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase32 hcase41
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase131b hcase001a hcase001b hcase330a hcase330b hcase341a hcase341b hcase401a hcase420a hcase420b hcase431a hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase32 hcase41 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase131b hcase001a hcase001b hcase330a hcase330b hcase341a hcase341b hcase401a hcase421a hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase32 hcase41 hcase43 hcase44
                      omega
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase301a hcase131a hcase001a hcase310b hcase340b hcase430b hcase420b hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase40 hcase41 hcase44
                        omega
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase301a hcase131a hcase001a hcase331a hcase310b hcase340b hcase430a hcase430b hcase421a hcase421b hcase320b hcase03 hcase10 hcase11 hcase12 hcase14 hcase40 hcase41 hcase44
                          omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat1 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase131a hcase001a hcase331a hcase310b hcase340a hcase340b hcase430b hcase421a hcase321a hcase400b hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase131b hcase001a hcase001b hcase331a hcase331b hcase310a hcase310b hcase340a hcase340b hcase430a hcase430b hcase421a hcase321a hcase321b hcase401a hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase44
                            omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase301a hcase131a hcase001a hcase331a hcase310b hcase340b hcase431a hcase431b hcase420a hcase420b hcase320b hcase03 hcase10 hcase11 hcase12 hcase14 hcase40 hcase41 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase001a hcase331a hcase310a hcase310b hcase340a hcase340b hcase431a hcase420b hcase03 hcase10 hcase11 hcase12 hcase14 hcase40 hcase41 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase131b hcase001a hcase001b hcase331a hcase331b hcase310a hcase310b hcase340a hcase340b hcase431a hcase421a hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase40 hcase41 hcase44
                        omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut6 hcut39 hcut5 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase131a hcase001a hcase331a hcase331b hcase310a hcase310b hcase341a hcase341b hcase400b hcase420b hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase41 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010a hcase010b hcase131a hcase001a hcase331a hcase310a hcase310b hcase341a hcase400b hcase421a hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase41 hcase43 hcase44
                        omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase001a hcase310a hcase310b hcase341a hcase341b hcase401a hcase430b hcase420b hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase41 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase131b hcase001a hcase001b hcase331a hcase331b hcase310a hcase310b hcase341a hcase341b hcase401a hcase430a hcase430b hcase421a hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase41 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase131b hcase001a hcase001b hcase331a hcase331b hcase310a hcase310b hcase341a hcase341b hcase401a hcase431a hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase41 hcase42 hcase44
                        omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut6 hcut39 hcut5 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010b hcase131a hcase001a hcase331a hcase331b hcase311a hcase311b hcase420b hcase400b hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase34 hcase41 hcase43 hcase44
                      omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut41 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase001a hcase311a hcase311b hcase420b hcase401a hcase430b hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase34 hcase41 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase131b hcase001a hcase001b hcase331a hcase331b hcase311a hcase311b hcase420a hcase420b hcase401a hcase431a hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase34 hcase41 hcase44
                        omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hcut66 hcut51 hcut81 hcut63 hcut69 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut6 hcut39 hcut5 hcut38 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase031a hcase040b hcase020a hcase020b hcase010a hcase010b hcase131a hcase001a hcase331a hcase311a hcase421a hcase400b hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase34 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase031a hcase031b hcase040a hcase040b hcase020a hcase020b hcase010a hcase010b hcase301a hcase301b hcase131a hcase131b hcase001a hcase001b hcase331a hcase331b hcase311a hcase311b hcase421a hcase401a hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase34 hcase41 hcase43 hcase44
                      omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase031a hcase040a hcase040b hcase020a hcase020b hcase011a hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase031a hcase040a hcase040b hcase021a hcase00 hcase01 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega
  ·
    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut51 hcut81 hcut63 hcut69 hcut60 hcut74 hcut50 hcut68 hcut82 hcut55 hcut76 hcut67 hcut56 hcut49 hcut0 hcut48 hcut17 hcut12 hcut47 hcut15 hcut46 hcut13 hcut10 hcut41 hcut6 hcut39 hcut5 hcut38 hcut2 hcut37 hcut36 hcut1 hcut35 hcut34 hcut33 hcut32 hcut30 hcut29 hcut26 hcut23 hcut25 hcut20 hcut19 hcut18 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase031a hcase041a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
    omega

#print axioms symbolic_v2_mask7_integer_shard003
end Jsp404.SixExactFloorKernel
