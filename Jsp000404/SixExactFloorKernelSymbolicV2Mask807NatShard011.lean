import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask807_integer_shard011 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut59 : (s02 + s03 + s10 + s11 + s14 + s42 + u02 + u03 + u10 + u11 + u14 + u42) + 1 ≤ (n + 1))
    (hcut67 : (s10 + s42 + u10 + u42) + 1 ≤ (n))
    (hcut65 : (s02 + s30 + s33 + u02 + u30 + u33) + 1 ≤ (n))
    (hcut13 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 1))
    (hcut10 : (s00 + s04 + s31 + s43 + u00 + u04 + u31 + u43 + 1) + 1 ≤ (2 * n))
    (hcut68 : (s12 + s30 + u12 + u30 + 1) + 1 ≤ (n))
    (hcut5 : (s34 + s41 + s42 + s43 + u34 + u41 + u42 + u43) + 1 ≤ (n))
    (hcut40 : (s01 + s43 + u01 + u43) + 1 ≤ (n))
    (hcut23 : (s13 + s31 + u13 + u31 + 1) + 1 ≤ (n))
    (hcut6 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut34 : (s02 + s41 + s42 + u02 + u41 + u42 + 1) + 1 ≤ (n))
    (hcut36 : (s02 + s33 + s42 + u02 + u33 + u42 + 1) + 1 ≤ (n))
    (hcut3 : (s03 + s32 + u03 + u32) + 1 ≤ (s13 + 2))
    (hcut62 : (s40 + u40) + 1 ≤ (s30 + 2))
    (hcut0 : (s12 + s30 + s32 + s33 + s34 + s41 + u12 + u30 + u32 + u33 + u34 + u41) + 1 ≤ (n + 1))
    (hcut52 : (s13 + s14 + s30 + s31 + u13 + u14 + u30 + u31) + 1 ≤ (n + 1))
    (hcut49 : (s13 + s14 + s30 + u13 + u14 + u30) + 1 ≤ (n))
    (hcut9 : (s00 + s31 + s40 + s43 + u00 + u31 + u40 + u43) + 1 ≤ (2 * n))
    (hcut4 : (s02 + s42 + u02 + u42) + 1 ≤ (s12 + s32 + 4))
    (hcut42 : (s01 + s02 + u01 + u02 + 1) + 1 ≤ (n))
    (hcut63 : (s02 + s30 + s34 + u02 + u30 + u34) + 1 ≤ (n + 1))
    (hcut20 : (s00 + s04 + s13 + s31 + s44 + u00 + u04 + u13 + u31 + u44) + 1 ≤ (2 * n + 1))
    (hcut61 : (s01 + s44 + u01 + u44) + 1 ≤ (n + 1))
    (hcut64 : (s02 + s30 + s34 + s41 + u02 + u30 + u34 + u41) + 1 ≤ (n + 1))
    (hcut22 : (s00 + s04 + s13 + s43 + u00 + u04 + u13 + u43 + 1) + 1 ≤ (2 * n))
    (hcut50 : (s01 + s03 + u01 + u03 + 1) + 1 ≤ (n))
    (hcut46 : (s01 + s10 + s43 + s44 + u01 + u10 + u43 + u44) + 1 ≤ (n + 2))
    (hcut58 : (s02 + s03 + s11 + s14 + s42 + u02 + u03 + u11 + u14 + u42) + 1 ≤ (n))
    (hcut72 : (s00 + s30 + s43 + u00 + u30 + u43 + 1) + 1 ≤ (2 * n))
    (hcut41 : (s01 + s10 + s44 + u01 + u10 + u44) + 1 ≤ (n + 2))
    (hcut55 : (s02 + s33 + s34 + s41 + u02 + u33 + u34 + u41) + 1 ≤ (n))
    (hcut2 : (s00 + s04 + s13 + s31 + s40 + s43 + s44 + u00 + u04 + u13 + u31 + u40 + u43 + u44) + 1 ≤ (2 * n + 2))
    (hcut70 : (s30 + s34 + s42 + s43 + u30 + u34 + u42 + u43) + 1 ≤ (n + 1))
    (hcut47 : (s00 + s01 + s43 + s44 + u00 + u01 + u43 + u44) + 1 ≤ (n + 2))
    (hcut18 : (s10 + s33 + s34 + s42 + u10 + u33 + u34 + u42) + 1 ≤ (n + 2))
    (hcut74 : (s30 + s41 + s43 + u30 + u41 + u43) + 1 ≤ (n))
    (hcut73 : (s00 + s13 + s30 + s31 + s43 + u00 + u13 + u30 + u31 + u43) + 1 ≤ (2 * n + 1))
    (hcut14 : (s14 + s31 + u14 + u31 + 1) + 1 ≤ (n))
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
    (hcase021a : 1 ≤ s02)
    (hcase021b : u02 = 1)
    : False := by
  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
  ·
    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
    ·
      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
      ·
        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
        ·
          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase000b hcase030b hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase040a hcase040b hcase000a hcase000b hcase031a hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase130a hcase130b hcase030a hcase030b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase310b hcase320b hcase300b hcase02 hcase10 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase130a hcase130b hcase030a hcase030b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase310b hcase320b hcase301a hcase02 hcase10 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase310a hcase310b hcase02 hcase10 hcase30 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase311a hcase311b hcase430b hcase400b hcase440b hcase02 hcase10 hcase30 hcase32 hcase33 hcase41 hcase42
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase311a hcase311b hcase430b hcase400b hcase441a hcase02 hcase10 hcase30 hcase32 hcase33 hcase41 hcase42
                            omega
                        ·
                          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase120b hcase110b hcase140b hcase311b hcase430a hcase430b hcase100b hcase02 hcase30 hcase32 hcase33 hcase41 hcase42 hcase44
                            omega
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                              ·
                                clear hn4 hsum_nat0 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase120b hcase110a hcase110b hcase140a hcase140b hcase311b hcase430b hcase401a hcase101a hcase410b hcase440b hcase02 hcase30 hcase32 hcase33 hcase42
                                omega
                              ·
                                clear hn4 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130b hcase030a hcase030b hcase120b hcase110a hcase110b hcase140a hcase140b hcase311b hcase430b hcase401a hcase101a hcase410b hcase441a hcase02 hcase30 hcase32 hcase33 hcase42
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase311a hcase311b hcase430a hcase430b hcase401a hcase101a hcase101b hcase411a hcase02 hcase30 hcase32 hcase33 hcase42 hcase44
                              omega
                      ·
                        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                        ·
                          clear hsum_nat0 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase120b hcase110b hcase140b hcase311a hcase311b hcase431a hcase431b hcase100b hcase02 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase44
                          omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                              ·
                                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                                ·
                                  clear hn4 hcut67 hcut65 hcut13 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase040a hcase040b hcase001a hcase340b hcase130b hcase030a hcase030b hcase120b hcase110a hcase110b hcase140a hcase140b hcase311a hcase431a hcase101a hcase400b hcase440b hcase320b hcase330b hcase02 hcase30 hcase41 hcase42
                                  omega
                                ·
                                  clear hn4 hsum_nat0 hsum_nat3 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut58 hcut72 hcut41 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase120b hcase110b hcase140b hcase311a hcase311b hcase431a hcase101a hcase400b hcase440a hcase440b hcase320a hcase320b hcase02 hcase30 hcase41 hcase42
                                  omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase311a hcase311b hcase431a hcase431b hcase101a hcase101b hcase400a hcase400b hcase440a hcase440b hcase02 hcase30 hcase33 hcase41 hcase42
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase120b hcase110b hcase140b hcase311a hcase311b hcase101a hcase400a hcase400b hcase02 hcase30 hcase32 hcase33 hcase41 hcase42
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase311a hcase311b hcase431a hcase101a hcase101b hcase401a hcase02 hcase30 hcase32 hcase33 hcase41 hcase42 hcase44
                            omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase120b hcase110a hcase110b hcase141a hcase100b hcase02 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase120b hcase110a hcase110b hcase141a hcase101a hcase02 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase120b hcase111a hcase100b hcase02 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase120b hcase111a hcase101a hcase02 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                            ·
                              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut5 hcut40 hcut23 hcut6 hcut34 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase130b hcase030a hcase030b hcase121a hcase140b hcase100b hcase110b hcase400a hcase400b hcase410a hcase410b hcase440a hcase440b hcase310b hcase320b hcase02 hcase30 hcase33 hcase42 hcase43
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase110a hcase110b hcase400a hcase400b hcase410a hcase410b hcase440a hcase440b hcase310a hcase310b hcase02 hcase30 hcase33 hcase42 hcase43
                                omega
                            ·
                              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase110a hcase110b hcase400b hcase410a hcase410b hcase440b hcase311a hcase311b hcase430b hcase02 hcase30 hcase32 hcase33 hcase42
                                omega
                              ·
                                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                                ·
                                  clear hn4 hcut59 hcut67 hcut65 hcut13 hcut5 hcut40 hcut23 hcut6 hcut34 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040a hcase040b hcase001a hcase340b hcase130b hcase030b hcase121a hcase140b hcase100b hcase110b hcase400b hcase410b hcase440b hcase311a hcase431a hcase320b hcase02 hcase30 hcase33 hcase42
                                  omega
                                ·
                                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase110a hcase110b hcase400a hcase400b hcase410a hcase410b hcase440a hcase440b hcase311a hcase311b hcase431a hcase431b hcase02 hcase30 hcase33 hcase42
                                  omega
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase110a hcase110b hcase400b hcase410a hcase410b hcase441a hcase430b hcase02 hcase30 hcase31 hcase32 hcase33 hcase42
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase110a hcase110b hcase400b hcase410a hcase410b hcase441a hcase431a hcase02 hcase30 hcase31 hcase32 hcase33 hcase42
                              omega
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase110a hcase110b hcase400b hcase411a hcase430b hcase02 hcase30 hcase31 hcase32 hcase33 hcase42 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase110a hcase110b hcase400a hcase400b hcase411a hcase431a hcase02 hcase30 hcase31 hcase32 hcase33 hcase42 hcase44
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase121a hcase140b hcase100b hcase110b hcase02 hcase30 hcase31 hcase32 hcase33 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase300a hcase300b hcase400b hcase430b hcase410b hcase02 hcase31 hcase32 hcase33 hcase42 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase111a hcase111b hcase300a hcase300b hcase400b hcase430b hcase411a hcase02 hcase31 hcase32 hcase33 hcase42 hcase44
                              omega
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase300a hcase300b hcase400b hcase431a hcase410b hcase02 hcase31 hcase32 hcase33 hcase42 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase111a hcase111b hcase300a hcase300b hcase400a hcase400b hcase431a hcase411a hcase02 hcase31 hcase32 hcase33 hcase42 hcase44
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase111a hcase111b hcase300b hcase02 hcase31 hcase32 hcase33 hcase41 hcase42 hcase43 hcase44
                          omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130b hcase030a hcase030b hcase121a hcase140a hcase140b hcase100b hcase111a hcase410b hcase400b hcase02 hcase31 hcase32 hcase33 hcase42 hcase43 hcase44
                            omega
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              clear hn4 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130b hcase030a hcase030b hcase121a hcase140a hcase140b hcase100b hcase111a hcase301a hcase410b hcase401a hcase430b hcase02 hcase31 hcase32 hcase33 hcase42 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase111a hcase111b hcase301a hcase301b hcase410a hcase410b hcase401a hcase431a hcase02 hcase31 hcase32 hcase33 hcase42 hcase44
                              omega
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase121a hcase140a hcase140b hcase100b hcase111a hcase301a hcase411a hcase430b hcase440b hcase02 hcase31 hcase32 hcase33 hcase40 hcase42
                              omega
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase111a hcase111b hcase301a hcase301b hcase411a hcase430b hcase441a hcase400b hcase02 hcase31 hcase32 hcase33 hcase42
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase111a hcase111b hcase301a hcase301b hcase411a hcase430a hcase430b hcase441a hcase441b hcase401a hcase02 hcase31 hcase32 hcase33 hcase42
                                omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase100a hcase100b hcase111a hcase111b hcase301a hcase301b hcase411a hcase431a hcase02 hcase31 hcase32 hcase33 hcase40 hcase42 hcase44
                            omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase440a hcase440b hcase300b hcase310b hcase320b hcase02 hcase11 hcase33 hcase40 hcase41 hcase43
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase440a hcase440b hcase300a hcase300b hcase310a hcase310b hcase02 hcase11 hcase33 hcase40 hcase41 hcase43
                              omega
                          ·
                            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                            ·
                              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                              ·
                                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                                ·
                                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                                  ·
                                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                                    ·
                                      clear hn4 hsum_nat0 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121b hcase140a hcase140b hcase101b hcase420b hcase440b hcase300a hcase300b hcase311a hcase311b hcase330a hcase330b hcase320a hcase320b hcase400b hcase410b hcase430b hcase02 hcase11
                                      omega
                                    ·
                                      clear hn4 hsum_nat0 hsum_nat1 hcut59 hcut67 hcut65 hcut13 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420b hcase440b hcase300b hcase311a hcase330b hcase320b hcase400b hcase410b hcase431a hcase02 hcase11
                                      omega
                                  ·
                                    clear hn4 hsum_nat1 hcut59 hcut67 hcut65 hcut13 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040a hcase040b hcase001a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase440b hcase300b hcase311a hcase330b hcase320b hcase400b hcase411a hcase02 hcase11 hcase43
                                    omega
                                ·
                                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase440a hcase440b hcase300b hcase311a hcase311b hcase330a hcase330b hcase320a hcase320b hcase02 hcase11 hcase41 hcase43
                                  omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase440a hcase440b hcase300a hcase300b hcase311a hcase311b hcase330a hcase330b hcase02 hcase11 hcase40 hcase41 hcase43
                                omega
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                                ·
                                  clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase440a hcase440b hcase300a hcase300b hcase311a hcase311b hcase400b hcase410b hcase02 hcase11 hcase32 hcase43
                                  omega
                                ·
                                  clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420b hcase440a hcase440b hcase300a hcase300b hcase311a hcase311b hcase400b hcase411a hcase02 hcase11 hcase32 hcase43
                                  omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase440a hcase440b hcase300b hcase311a hcase311b hcase331a hcase331b hcase02 hcase11 hcase32 hcase41 hcase43
                                omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420b hcase440b hcase400b hcase02 hcase11 hcase31 hcase32 hcase33 hcase41 hcase43
                            omega
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase140a hcase140b hcase101a hcase101b hcase420b hcase440b hcase301a hcase401a hcase410b hcase430b hcase02 hcase11 hcase31 hcase32 hcase33
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase440a hcase440b hcase301a hcase301b hcase401a hcase410a hcase410b hcase431a hcase02 hcase11 hcase31 hcase32 hcase33
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase440a hcase440b hcase301a hcase301b hcase401a hcase411a hcase02 hcase11 hcase31 hcase32 hcase33 hcase43
                              omega
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase441a hcase300a hcase300b hcase400b hcase430b hcase02 hcase11 hcase31 hcase32 hcase33 hcase41
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase441a hcase300a hcase300b hcase400b hcase431a hcase02 hcase11 hcase31 hcase32 hcase33 hcase41
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase441a hcase441b hcase300b hcase02 hcase11 hcase31 hcase32 hcase33 hcase41 hcase43
                            omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420b hcase441a hcase410b hcase400b hcase02 hcase11 hcase31 hcase32 hcase33 hcase43
                              omega
                            ·
                              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                              ·
                                clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420b hcase441a hcase301a hcase410b hcase401a hcase430b hcase02 hcase11 hcase31 hcase32 hcase33
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase441a hcase441b hcase301a hcase301b hcase410a hcase410b hcase401a hcase431a hcase02 hcase11 hcase31 hcase32 hcase33
                                omega
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase441a hcase301a hcase301b hcase411a hcase430b hcase400b hcase02 hcase11 hcase31 hcase32 hcase33
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase441a hcase441b hcase301a hcase301b hcase411a hcase430a hcase430b hcase401a hcase02 hcase11 hcase31 hcase32 hcase33
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase420a hcase420b hcase441a hcase441b hcase301a hcase301b hcase411a hcase431a hcase02 hcase11 hcase31 hcase32 hcase33 hcase40
                              omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase421a hcase400b hcase430b hcase02 hcase11 hcase30 hcase31 hcase32 hcase33 hcase41 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase421a hcase400a hcase400b hcase431a hcase02 hcase11 hcase30 hcase31 hcase32 hcase33 hcase41 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase140a hcase140b hcase101a hcase101b hcase421a hcase401a hcase02 hcase11 hcase30 hcase31 hcase32 hcase33 hcase41 hcase43 hcase44
                        omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase130a hcase130b hcase030a hcase030b hcase121b hcase141b hcase330b hcase310b hcase300b hcase02 hcase10 hcase11 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase130b hcase030a hcase030b hcase141a hcase141b hcase330b hcase310b hcase301a hcase02 hcase10 hcase11 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase130b hcase030a hcase030b hcase121a hcase121b hcase330b hcase311a hcase300b hcase02 hcase10 hcase11 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase330b hcase311a hcase301a hcase320b hcase02 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase121a hcase121b hcase141a hcase141b hcase330a hcase330b hcase311a hcase311b hcase301a hcase301b hcase02 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        clear hn4 hsum_nat1 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut3 hcut62 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase141a hcase141b hcase400b hcase310b hcase02 hcase10 hcase11 hcase30 hcase32 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              clear hn4 hsum_nat1 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase331a hcase400b hcase311a hcase300b hcase320b hcase410b hcase02 hcase10 hcase11 hcase42 hcase43 hcase44
                              omega
                            ·
                              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                              ·
                                clear hn4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130b hcase030a hcase030b hcase121a hcase331a hcase400b hcase311a hcase300a hcase300b hcase320a hcase320b hcase411a hcase100b hcase02 hcase11 hcase42 hcase43 hcase44
                                omega
                              ·
                                clear hn4 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130b hcase030a hcase030b hcase121a hcase331a hcase400b hcase311a hcase300a hcase300b hcase320a hcase320b hcase411a hcase101a hcase02 hcase11 hcase42 hcase43 hcase44
                                omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130b hcase030a hcase030b hcase121a hcase121b hcase141a hcase141b hcase331a hcase331b hcase400a hcase400b hcase311a hcase311b hcase300a hcase300b hcase02 hcase10 hcase11 hcase41 hcase42 hcase43 hcase44
                            omega
                        ·
                          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                          ·
                            clear hn4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130b hcase030a hcase030b hcase121a hcase331a hcase400b hcase311a hcase301a hcase100b hcase02 hcase11 hcase32 hcase41 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130b hcase030a hcase030b hcase121a hcase331a hcase400b hcase311a hcase301a hcase101a hcase02 hcase11 hcase32 hcase41 hcase42 hcase43 hcase44
                            omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase141a hcase141b hcase331a hcase331b hcase420a hcase420b hcase410a hcase410b hcase300b hcase02 hcase10 hcase11 hcase31 hcase32 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase130a hcase130b hcase030b hcase121a hcase121b hcase141a hcase141b hcase401a hcase420b hcase410b hcase301a hcase02 hcase10 hcase11 hcase31 hcase32 hcase43 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase141a hcase141b hcase331a hcase331b hcase401a hcase420a hcase420b hcase411a hcase02 hcase10 hcase11 hcase30 hcase31 hcase32 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase030a hcase030b hcase121a hcase121b hcase141a hcase141b hcase331a hcase331b hcase401a hcase421a hcase02 hcase10 hcase11 hcase30 hcase31 hcase32 hcase41 hcase43 hcase44
                        omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase130a hcase130b hcase031a hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase131a hcase131b hcase120a hcase120b hcase300b hcase310b hcase320b hcase02 hcase03 hcase10 hcase11 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase300a hcase300b hcase310a hcase310b hcase321a hcase321b hcase330a hcase330b hcase400b hcase430b hcase440b hcase02 hcase03 hcase10 hcase11 hcase14 hcase41 hcase42
                            omega
                          ·
                            clear hn4 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340b hcase131a hcase131b hcase120a hcase120b hcase300b hcase310b hcase321a hcase330b hcase400b hcase430b hcase441a hcase02 hcase03 hcase10 hcase11 hcase14 hcase41 hcase42
                            omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat1 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040a hcase040b hcase001a hcase340b hcase131a hcase120a hcase120b hcase300b hcase310b hcase321a hcase330b hcase400b hcase431a hcase440b hcase02 hcase03 hcase10 hcase11 hcase14 hcase41 hcase42
                            omega
                          ·
                            clear hn4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340b hcase131a hcase131b hcase120a hcase120b hcase300b hcase310b hcase321a hcase330b hcase400b hcase431a hcase441a hcase02 hcase03 hcase10 hcase11 hcase14 hcase41 hcase42
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase300b hcase310a hcase310b hcase321a hcase321b hcase330a hcase330b hcase02 hcase03 hcase10 hcase11 hcase14 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase300a hcase300b hcase310a hcase310b hcase321a hcase321b hcase030b hcase400b hcase410b hcase02 hcase10 hcase11 hcase14 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase300a hcase300b hcase310b hcase321a hcase331a hcase030a hcase030b hcase400a hcase400b hcase02 hcase10 hcase11 hcase14 hcase42 hcase43 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase300b hcase310a hcase310b hcase321a hcase321b hcase331a hcase331b hcase030a hcase030b hcase02 hcase10 hcase11 hcase14 hcase41 hcase42 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase300a hcase300b hcase310a hcase310b hcase321a hcase321b hcase331a hcase331b hcase031a hcase02 hcase10 hcase11 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          clear hn4 hsum_nat1 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut6 hcut34 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340b hcase120a hcase120b hcase300b hcase311a hcase400b hcase410b hcase030b hcase320b hcase02 hcase10 hcase11 hcase14 hcase33 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase131a hcase120a hcase120b hcase300b hcase311a hcase400a hcase400b hcase410a hcase410b hcase030a hcase030b hcase321a hcase330b hcase02 hcase10 hcase11 hcase14 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase300a hcase300b hcase311a hcase311b hcase400b hcase410b hcase030b hcase321a hcase321b hcase02 hcase10 hcase11 hcase14 hcase42 hcase43 hcase44
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase300a hcase300b hcase311a hcase311b hcase400a hcase400b hcase410a hcase410b hcase031a hcase02 hcase10 hcase11 hcase14 hcase32 hcase33 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                        ·
                          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase120a hcase120b hcase300b hcase311a hcase400a hcase400b hcase411a hcase411b hcase320b hcase030a hcase030b hcase330b hcase02 hcase10 hcase11 hcase14 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase120b hcase300b hcase311a hcase400b hcase411a hcase320b hcase030b hcase331a hcase02 hcase10 hcase11 hcase14 hcase42 hcase43 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase300a hcase300b hcase311a hcase311b hcase400a hcase400b hcase411a hcase411b hcase320a hcase320b hcase031a hcase02 hcase10 hcase11 hcase14 hcase33 hcase42 hcase43 hcase44
                          omega
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase131a hcase120a hcase120b hcase300b hcase311a hcase400a hcase400b hcase411a hcase411b hcase321a hcase330b hcase02 hcase03 hcase10 hcase11 hcase14 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat1 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase120a hcase120b hcase300b hcase311a hcase400b hcase411a hcase321a hcase331a hcase420b hcase02 hcase03 hcase10 hcase11 hcase14 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase300a hcase300b hcase311a hcase311b hcase400a hcase400b hcase411a hcase321a hcase321b hcase331a hcase331b hcase421a hcase02 hcase03 hcase10 hcase11 hcase14 hcase43 hcase44
                            omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase300b hcase311a hcase311b hcase02 hcase03 hcase10 hcase11 hcase14 hcase32 hcase33 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase320b hcase330a hcase330b hcase310b hcase02 hcase03 hcase10 hcase11 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase120a hcase120b hcase301a hcase320b hcase330b hcase311a hcase02 hcase03 hcase10 hcase11 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase320b hcase331a hcase310b hcase02 hcase03 hcase10 hcase11 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut59 hcut67 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase131a hcase120b hcase320b hcase331a hcase311a hcase100b hcase110b hcase02 hcase03 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              clear hn4 hcut67 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040b hcase001a hcase340b hcase131a hcase120b hcase320b hcase331a hcase311a hcase100a hcase100b hcase111a hcase400b hcase410b hcase02 hcase03 hcase14 hcase42 hcase43 hcase44
                              omega
                            ·
                              clear hn4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut72 hcut41 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase120b hcase301a hcase320b hcase331a hcase311a hcase100b hcase111a hcase400b hcase411a hcase02 hcase03 hcase14 hcase42 hcase43 hcase44
                              omega
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                              ·
                                clear hn4 hcut59 hcut67 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase040b hcase001a hcase340b hcase131a hcase120b hcase301a hcase320b hcase331a hcase311a hcase100b hcase111a hcase401a hcase430b hcase410b hcase02 hcase03 hcase14 hcase42 hcase44
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase320a hcase320b hcase331a hcase331b hcase311a hcase311b hcase100a hcase100b hcase111a hcase111b hcase401a hcase430a hcase430b hcase411a hcase02 hcase03 hcase14 hcase42 hcase44
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase320a hcase320b hcase331a hcase331b hcase311a hcase311b hcase100a hcase100b hcase111a hcase111b hcase401a hcase431a hcase02 hcase03 hcase14 hcase41 hcase42 hcase44
                              omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              clear hn4 hcut67 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040b hcase001a hcase340b hcase131a hcase120b hcase320b hcase331a hcase311a hcase101a hcase400b hcase030a hcase030b hcase410b hcase02 hcase11 hcase14 hcase42 hcase43 hcase44
                              omega
                            ·
                              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                              ·
                                clear hn4 hsum_nat1 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase120a hcase120b hcase301a hcase320b hcase331a hcase311a hcase101a hcase101b hcase400b hcase030b hcase411a hcase420b hcase02 hcase11 hcase14 hcase43 hcase44
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase320a hcase320b hcase331a hcase331b hcase311a hcase311b hcase101a hcase101b hcase400a hcase400b hcase030a hcase030b hcase411a hcase421a hcase02 hcase11 hcase14 hcase43 hcase44
                                omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase320a hcase320b hcase331a hcase331b hcase311a hcase311b hcase101a hcase101b hcase400a hcase400b hcase031a hcase02 hcase11 hcase14 hcase41 hcase42 hcase43 hcase44
                            omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                            ·
                              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                              ·
                                clear hn4 hsum_nat1 hcut59 hcut67 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340b hcase120a hcase120b hcase301a hcase320b hcase331a hcase311a hcase101a hcase101b hcase401a hcase410b hcase030b hcase420b hcase02 hcase11 hcase14 hcase43 hcase44
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase320a hcase320b hcase331a hcase331b hcase311a hcase311b hcase101a hcase101b hcase401a hcase410a hcase410b hcase030a hcase030b hcase421a hcase02 hcase11 hcase14 hcase43 hcase44
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase320a hcase320b hcase331a hcase331b hcase311a hcase311b hcase101a hcase101b hcase401a hcase401b hcase410a hcase410b hcase031a hcase02 hcase11 hcase14 hcase42 hcase43 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase320a hcase320b hcase331a hcase331b hcase311a hcase311b hcase101a hcase101b hcase401a hcase411a hcase02 hcase03 hcase11 hcase14 hcase42 hcase43 hcase44
                            omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase321a hcase321b hcase400b hcase410b hcase030b hcase420b hcase430b hcase02 hcase10 hcase11 hcase14 hcase31 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase321a hcase321b hcase400b hcase410b hcase030b hcase420b hcase431a hcase02 hcase10 hcase11 hcase14 hcase31 hcase33 hcase44
                            omega
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase321a hcase321b hcase400b hcase410a hcase410b hcase030b hcase421a hcase430b hcase02 hcase10 hcase11 hcase14 hcase31 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase321a hcase321b hcase400a hcase400b hcase410a hcase410b hcase030a hcase030b hcase421a hcase431a hcase02 hcase10 hcase11 hcase14 hcase31 hcase33 hcase44
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase321a hcase321b hcase400a hcase400b hcase410a hcase410b hcase031a hcase02 hcase10 hcase11 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase321a hcase321b hcase400b hcase411a hcase430b hcase030b hcase02 hcase10 hcase11 hcase14 hcase31 hcase33 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase321a hcase321b hcase400a hcase400b hcase411a hcase411b hcase430a hcase430b hcase031a hcase02 hcase10 hcase11 hcase14 hcase31 hcase33 hcase42 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase321a hcase321b hcase400a hcase400b hcase411a hcase431a hcase02 hcase03 hcase10 hcase11 hcase14 hcase31 hcase33 hcase42 hcase44
                        omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                          ·
                            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut0 hcut52 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase120b hcase301a hcase321a hcase321b hcase401a hcase310a hcase310b hcase430b hcase440b hcase100b hcase110b hcase02 hcase03 hcase14 hcase33 hcase41 hcase42
                              omega
                            ·
                              clear hn4 hsum_nat0 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut52 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase120a hcase120b hcase301a hcase321a hcase401a hcase310b hcase430b hcase440b hcase100b hcase111a hcase02 hcase03 hcase14 hcase33 hcase41 hcase42
                              omega
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase120b hcase301a hcase321a hcase321b hcase401a hcase310a hcase310b hcase430b hcase440b hcase101a hcase410b hcase02 hcase03 hcase11 hcase14 hcase33 hcase42
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase321a hcase321b hcase401a hcase310a hcase310b hcase430a hcase430b hcase440a hcase440b hcase101a hcase101b hcase411a hcase02 hcase03 hcase11 hcase14 hcase33 hcase42
                              omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              clear hn4 hsum_nat1 hcut59 hcut67 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut0 hcut52 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340b hcase131a hcase120a hcase120b hcase301a hcase321a hcase401a hcase310b hcase430b hcase441a hcase410b hcase420b hcase02 hcase03 hcase10 hcase11 hcase14 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase321a hcase321b hcase401a hcase310a hcase310b hcase430a hcase430b hcase441a hcase441b hcase410a hcase410b hcase421a hcase02 hcase03 hcase10 hcase11 hcase14 hcase33
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase321a hcase321b hcase401a hcase310a hcase310b hcase430a hcase430b hcase441a hcase441b hcase411a hcase02 hcase03 hcase10 hcase11 hcase14 hcase33 hcase42
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase321a hcase321b hcase401a hcase310a hcase310b hcase431a hcase02 hcase03 hcase10 hcase11 hcase14 hcase33 hcase41 hcase42 hcase44
                        omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase120a hcase120b hcase301a hcase321a hcase321b hcase401a hcase410b hcase420b hcase030a hcase030b hcase430b hcase440b hcase02 hcase10 hcase11 hcase14 hcase33
                                omega
                              ·
                                clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase321a hcase321b hcase401a hcase311a hcase311b hcase410b hcase420b hcase030b hcase430b hcase441a hcase02 hcase10 hcase11 hcase14 hcase33
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase321a hcase321b hcase401a hcase311a hcase311b hcase410a hcase410b hcase420a hcase420b hcase030a hcase030b hcase431a hcase02 hcase10 hcase11 hcase14 hcase33 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase321a hcase321b hcase401a hcase401b hcase311a hcase311b hcase410a hcase410b hcase420a hcase420b hcase031a hcase02 hcase10 hcase11 hcase14 hcase33 hcase43 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase321a hcase321b hcase401a hcase311a hcase311b hcase410a hcase410b hcase421a hcase02 hcase03 hcase10 hcase11 hcase14 hcase33 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase120a hcase120b hcase301a hcase301b hcase321a hcase321b hcase401a hcase311a hcase311b hcase411a hcase02 hcase03 hcase10 hcase11 hcase14 hcase33 hcase42 hcase43 hcase44
                        omega
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase131a hcase131b hcase121a hcase121b hcase030a hcase030b hcase420a hcase420b hcase430a hcase430b hcase400a hcase400b hcase300b hcase310b hcase320b hcase02 hcase10 hcase11 hcase14 hcase33 hcase41 hcase44
                            omega
                          ·
                            clear hn4 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut62 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340b hcase131a hcase131b hcase030a hcase030b hcase420a hcase420b hcase430b hcase400b hcase300b hcase310b hcase321a hcase02 hcase10 hcase11 hcase14 hcase33 hcase41 hcase44
                            omega
                        ·
                          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                          ·
                            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase121a hcase121b hcase030a hcase030b hcase420a hcase420b hcase430a hcase430b hcase400a hcase400b hcase300b hcase311a hcase330b hcase320b hcase02 hcase10 hcase11 hcase14 hcase41 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase131a hcase121a hcase121b hcase030a hcase030b hcase420a hcase420b hcase430a hcase430b hcase400a hcase400b hcase300b hcase311a hcase330b hcase321a hcase02 hcase10 hcase11 hcase14 hcase41 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase030b hcase420b hcase430b hcase400b hcase300a hcase300b hcase311a hcase311b hcase02 hcase10 hcase11 hcase14 hcase32 hcase41 hcase44
                            omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase030b hcase420b hcase430b hcase400b hcase410b hcase02 hcase10 hcase11 hcase14 hcase31 hcase32 hcase33 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase030b hcase420a hcase420b hcase430b hcase400b hcase301a hcase301b hcase411a hcase02 hcase10 hcase11 hcase14 hcase31 hcase32 hcase33 hcase44
                          omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase030a hcase030b hcase420a hcase420b hcase430a hcase430b hcase410a hcase410b hcase300b hcase02 hcase10 hcase11 hcase14 hcase31 hcase32 hcase33 hcase44
                          omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase030a hcase030b hcase420b hcase430b hcase401a hcase410b hcase301a hcase301b hcase440b hcase02 hcase10 hcase11 hcase14 hcase31 hcase32 hcase33
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase030b hcase420b hcase430b hcase401a hcase410b hcase301a hcase441a hcase02 hcase10 hcase11 hcase14 hcase31 hcase32 hcase33
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase030a hcase030b hcase420a hcase420b hcase430a hcase430b hcase401a hcase411a hcase02 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase44
                        omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase131a hcase131b hcase121a hcase121b hcase030a hcase030b hcase420a hcase420b hcase431a hcase431b hcase410a hcase410b hcase300b hcase320b hcase310b hcase02 hcase10 hcase11 hcase14 hcase33 hcase40 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut6 hcut34 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340b hcase121a hcase121b hcase030b hcase420a hcase420b hcase431a hcase410b hcase300b hcase320b hcase311a hcase02 hcase10 hcase11 hcase14 hcase33 hcase40 hcase44
                            omega
                        ·
                          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                          ·
                            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase131a hcase131b hcase121b hcase030a hcase030b hcase420a hcase420b hcase431a hcase431b hcase410a hcase410b hcase300b hcase321a hcase330b hcase310b hcase02 hcase10 hcase11 hcase14 hcase40 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut6 hcut34 hcut36 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340b hcase131a hcase121a hcase121b hcase030a hcase030b hcase420a hcase420b hcase431a hcase431b hcase410a hcase410b hcase300b hcase321a hcase330b hcase311a hcase02 hcase10 hcase11 hcase14 hcase40 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase030b hcase420a hcase420b hcase431a hcase410b hcase300b hcase321a hcase321b hcase02 hcase10 hcase11 hcase14 hcase31 hcase40 hcase44
                            omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase030b hcase420b hcase431a hcase410b hcase400b hcase02 hcase10 hcase11 hcase14 hcase31 hcase32 hcase33 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase030a hcase030b hcase420a hcase420b hcase431a hcase410a hcase410b hcase301a hcase301b hcase401a hcase02 hcase10 hcase11 hcase14 hcase31 hcase32 hcase33 hcase44
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase030a hcase030b hcase420a hcase420b hcase431a hcase411a hcase02 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase44
                      omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase030b hcase421a hcase400b hcase430b hcase02 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase41 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase030a hcase030b hcase421a hcase400a hcase400b hcase431a hcase02 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase41 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase030a hcase030b hcase421a hcase401a hcase02 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase41 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase340a hcase340b hcase131a hcase131b hcase121a hcase121b hcase031a hcase02 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase400b hcase430b hcase030b hcase420b hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase41 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase341a hcase341b hcase400b hcase430b hcase030b hcase421a hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase41 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase400a hcase400b hcase430a hcase430b hcase031a hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase41 hcase42 hcase44
                omega
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut2 hcut70 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010a hcase010b hcase040b hcase001a hcase400b hcase431a hcase030b hcase420b hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase41 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase400a hcase400b hcase431a hcase030a hcase030b hcase421a hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase41 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase400a hcase400b hcase431a hcase431b hcase031a hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase41 hcase42 hcase44
                omega
          ·
            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase430a hcase430b hcase300b hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase41 hcase42 hcase44
                omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut67 hcut65 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase010b hcase040b hcase001a hcase401a hcase430b hcase301a hcase420b hcase030b hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase41 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase401a hcase401b hcase430a hcase430b hcase301a hcase301b hcase420a hcase420b hcase031a hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase41 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase401a hcase430a hcase430b hcase301a hcase301b hcase421a hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase41 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase401a hcase431a hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase41 hcase42 hcase44
              omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase010a hcase010b hcase041a hcase00 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega
  ·
    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut67 hcut65 hcut13 hcut10 hcut68 hcut5 hcut40 hcut23 hcut6 hcut34 hcut36 hcut3 hcut62 hcut0 hcut52 hcut49 hcut9 hcut4 hcut42 hcut63 hcut20 hcut61 hcut64 hcut22 hcut50 hcut46 hcut58 hcut72 hcut41 hcut55 hcut2 hcut70 hcut47 hcut18 hcut74 hcut73 hcut14 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase011a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
    omega

#print axioms symbolic_v2_mask807_integer_shard011
end Jsp404.SixExactFloorKernel
