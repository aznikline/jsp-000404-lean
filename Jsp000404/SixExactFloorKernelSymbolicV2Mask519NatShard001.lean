import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask519_integer_shard001 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut26 : (s12 + s14 + s30 + u12 + u14 + u30) + 1 ≤ (n))
    (hcut30 : (s30 + s31 + u30 + u31 + 2) + 1 ≤ (n))
    (hcut35 : (s00 + s04 + s40 + s44 + u00 + u04 + u40 + u44) + 1 ≤ (2 * n))
    (hcut31 : (s00 + s32 + u00 + u32) + 1 ≤ (n))
    (hcut63 : (s01 + s13 + s14 + s32 + s40 + s43 + s44 + u01 + u13 + u14 + u32 + u40 + u43 + u44) + 1 ≤ (2 * n + 1))
    (hcut13 : (s02 + s42 + u02 + u42) + 1 ≤ (s32 + 2))
    (hcut44 : (s00 + s04 + s13 + s40 + s44 + u00 + u04 + u13 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut69 : (s00 + s01 + s04 + s32 + s34 + s40 + u00 + u01 + u04 + u32 + u34 + u40) + 1 ≤ (2 * n))
    (hcut12 : (s43 + u43) + 1 ≤ (s33 + 2))
    (hcut74 : (s00 + s04 + s13 + s40 + s42 + s44 + u00 + u04 + u13 + u40 + u42 + u44) + 1 ≤ (2 * n + 2))
    (hcut64 : (s00 + s01 + s32 + s33 + u00 + u01 + u32 + u33) + 1 ≤ (n + 1))
    (hcut71 : (s00 + s01 + s04 + s33 + s34 + s40 + u00 + u01 + u04 + u33 + u34 + u40) + 1 ≤ (2 * n))
    (hcut65 : (s00 + s01 + s32 + s43 + s44 + u00 + u01 + u32 + u43 + u44) + 1 ≤ (n + 2))
    (hcut23 : (s02 + s03 + s04 + u02 + u03 + u04) + 1 ≤ (n))
    (hcut58 : (s00 + s01 + s43 + s44 + u00 + u01 + u43 + u44) + 1 ≤ (n + 1))
    (hcut2 : (s00 + s04 + s13 + s33 + s34 + s40 + s42 + u00 + u04 + u13 + u33 + u34 + u40 + u42) + 1 ≤ (2 * n + 2))
    (hcut53 : (s00 + s01 + s33 + u00 + u01 + u33) + 1 ≤ (n))
    (hcut48 : (s00 + s04 + s32 + s40 + s43 + s44 + u00 + u04 + u32 + u40 + u43 + u44) + 1 ≤ (2 * n + 1))
    (hcut6 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut21 : (s03 + s41 + u03 + u41) + 1 ≤ (s13 + 2))
    (hcut59 : (s01 + s32 + u01 + u32 + 1) + 1 ≤ (n))
    (hcut3 : (s12 + s30 + s33 + s34 + s41 + s42 + u12 + u30 + u33 + u34 + u41 + u42) + 1 ≤ (n + 1))
    (hcut51 : (s00 + s02 + s04 + s13 + s40 + s44 + u00 + u02 + u04 + u13 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut72 : (s33 + s34 + s40 + u33 + u34 + u40) + 1 ≤ (n + 1))
    (hcut38 : (s31 + s32 + s40 + s44 + u31 + u32 + u40 + u44) + 1 ≤ (n + s12 + 3))
    (hcut56 : (s01 + s43 + s44 + u01 + u43 + u44) + 1 ≤ (n))
    (hcut5 : (s04 + s13 + s40 + u04 + u13 + u40) + 1 ≤ (n + 2))
    (hcut42 : (s13 + s40 + u13 + u40) + 1 ≤ (n))
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
    (hcase010a : s01 = 0)
    (hcase010b : u01 = 0)
    (hcase001a : 1 ≤ s00)
    (hcase001b : u00 = 1)
    (hcase100a : s10 = 0)
    (hcase100b : u10 = 0)
    (hcase110a : s11 = 0)
    (hcase110b : u11 = 0)
    : False := by
  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
  ·
    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
    ·
      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
      ·
        clear hsum_nat0 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100b hcase110b hcase140b hcase120b hcase130b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
      ·
        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
        ·
          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hsum_nat0 hsum_nat1 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320b hcase020a hcase020b hcase040a hcase040b hcase340b hcase300b hcase310b hcase330b hcase00 hcase01 hcase03 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320b hcase020a hcase020b hcase040a hcase040b hcase340b hcase300b hcase310b hcase331a hcase00 hcase01 hcase03 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat4 hcut26 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320b hcase020b hcase040b hcase340b hcase300a hcase300b hcase311a hcase430a hcase430b hcase440a hcase440b hcase030b hcase00 hcase01 hcase10 hcase11 hcase33 hcase40 hcase41 hcase42
                          omega
                        ·
                          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut26 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320b hcase020a hcase020b hcase040a hcase040b hcase340b hcase300a hcase300b hcase311a hcase430a hcase430b hcase440a hcase440b hcase031a hcase031b hcase330b hcase00 hcase01 hcase10 hcase11 hcase40 hcase41 hcase42
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut26 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase320b hcase020a hcase020b hcase040b hcase340b hcase300a hcase300b hcase311a hcase430b hcase440b hcase031a hcase331a hcase00 hcase01 hcase10 hcase11 hcase40 hcase41 hcase42
                            omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat4 hcut26 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320b hcase020b hcase040b hcase340b hcase300a hcase300b hcase311a hcase430a hcase430b hcase441a hcase441b hcase400a hcase400b hcase030b hcase00 hcase01 hcase10 hcase11 hcase33 hcase41 hcase42
                            omega
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020b hcase040b hcase340a hcase340b hcase300a hcase300b hcase311a hcase311b hcase430a hcase430b hcase441a hcase400b hcase031a hcase420b hcase00 hcase01 hcase10 hcase11 hcase33 hcase41
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320b hcase020a hcase020b hcase040a hcase040b hcase340a hcase340b hcase300a hcase300b hcase311a hcase311b hcase430a hcase430b hcase441a hcase441b hcase400a hcase400b hcase031a hcase031b hcase00 hcase01 hcase10 hcase11 hcase33 hcase41
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100b hcase110b hcase140b hcase120b hcase131a hcase320a hcase320b hcase020a hcase020b hcase040a hcase040b hcase340a hcase340b hcase300a hcase300b hcase311a hcase311b hcase430a hcase430b hcase441a hcase441b hcase00 hcase01 hcase03 hcase10 hcase11 hcase33 hcase41 hcase42
                          omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020b hcase040b hcase340a hcase340b hcase300a hcase300b hcase311a hcase311b hcase400a hcase400b hcase420a hcase420b hcase030b hcase00 hcase01 hcase10 hcase11 hcase33 hcase41 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020b hcase040b hcase340a hcase340b hcase300a hcase300b hcase311a hcase311b hcase431a hcase400b hcase420b hcase031a hcase00 hcase01 hcase10 hcase11 hcase33 hcase41 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020a hcase020b hcase040a hcase040b hcase340a hcase340b hcase300a hcase300b hcase311a hcase311b hcase431a hcase400a hcase400b hcase421a hcase00 hcase01 hcase03 hcase10 hcase11 hcase33 hcase41 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020a hcase020b hcase040a hcase040b hcase340a hcase340b hcase300a hcase300b hcase311a hcase311b hcase431a hcase401a hcase00 hcase01 hcase03 hcase10 hcase11 hcase33 hcase41 hcase42 hcase44
                        omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut26 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320b hcase020a hcase020b hcase040a hcase040b hcase340b hcase301a hcase330b hcase00 hcase01 hcase03 hcase10 hcase11 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hcut26 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320b hcase020a hcase020b hcase040b hcase340b hcase301a hcase331a hcase400b hcase430b hcase440b hcase00 hcase01 hcase03 hcase10 hcase11 hcase31 hcase41 hcase42
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat4 hcut26 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320b hcase020b hcase040b hcase340b hcase301a hcase331a hcase400a hcase400b hcase430a hcase430b hcase441a hcase441b hcase420a hcase420b hcase030b hcase00 hcase01 hcase10 hcase11 hcase31 hcase41
                              omega
                            ·
                              clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020b hcase040b hcase340a hcase340b hcase301a hcase301b hcase331a hcase331b hcase400b hcase430a hcase430b hcase441a hcase420b hcase031a hcase00 hcase01 hcase10 hcase11 hcase31 hcase41
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320b hcase020a hcase020b hcase040a hcase040b hcase340a hcase340b hcase301a hcase301b hcase331a hcase331b hcase400a hcase400b hcase430a hcase430b hcase441a hcase441b hcase00 hcase01 hcase03 hcase10 hcase11 hcase31 hcase41
                            omega
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat4 hcut26 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320b hcase020b hcase040b hcase340b hcase301a hcase331a hcase400a hcase400b hcase431a hcase431b hcase420a hcase420b hcase030b hcase00 hcase01 hcase10 hcase11 hcase31 hcase41 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020b hcase040b hcase340a hcase340b hcase301a hcase301b hcase331a hcase331b hcase400b hcase431a hcase420b hcase031a hcase00 hcase01 hcase10 hcase11 hcase31 hcase41 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020a hcase020b hcase040a hcase040b hcase340a hcase340b hcase301a hcase301b hcase331a hcase331b hcase400a hcase400b hcase431a hcase421a hcase00 hcase01 hcase03 hcase10 hcase11 hcase31 hcase41 hcase44
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100b hcase110b hcase140b hcase120b hcase131a hcase320a hcase320b hcase020a hcase020b hcase040a hcase040b hcase340a hcase340b hcase301a hcase301b hcase331a hcase331b hcase00 hcase01 hcase03 hcase10 hcase11 hcase31 hcase41 hcase42 hcase43 hcase44
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
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020a hcase020b hcase040a hcase040b hcase341a hcase341b hcase400b hcase410b hcase420b hcase430b hcase440b hcase00 hcase01 hcase03 hcase10 hcase11 hcase30 hcase31 hcase33
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020a hcase020b hcase040a hcase040b hcase341a hcase341b hcase400b hcase410b hcase420b hcase430a hcase430b hcase441a hcase00 hcase01 hcase03 hcase10 hcase11 hcase30 hcase31 hcase33
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020a hcase020b hcase040a hcase040b hcase341a hcase341b hcase400b hcase410b hcase420b hcase431a hcase00 hcase01 hcase03 hcase10 hcase11 hcase30 hcase31 hcase33 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320b hcase020a hcase020b hcase040a hcase040b hcase341a hcase341b hcase400a hcase400b hcase410a hcase410b hcase00 hcase01 hcase03 hcase10 hcase11 hcase30 hcase31 hcase33 hcase43 hcase44
                      omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020a hcase020b hcase040a hcase040b hcase400b hcase411a hcase430b hcase440b hcase00 hcase01 hcase03 hcase10 hcase11 hcase30 hcase31 hcase33 hcase42
                        omega
                      ·
                        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020b hcase040b hcase341a hcase341b hcase400a hcase400b hcase411a hcase411b hcase430a hcase430b hcase030b hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase33 hcase42
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320b hcase020a hcase020b hcase040b hcase341a hcase341b hcase400b hcase411a hcase430a hcase430b hcase441a hcase031a hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase33 hcase42
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020a hcase020b hcase040a hcase040b hcase341a hcase341b hcase400a hcase400b hcase411a hcase431a hcase00 hcase01 hcase03 hcase10 hcase11 hcase30 hcase31 hcase33 hcase42 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100b hcase110b hcase140b hcase120b hcase131a hcase320a hcase320b hcase020a hcase020b hcase040a hcase040b hcase341a hcase341b hcase00 hcase01 hcase03 hcase10 hcase11 hcase30 hcase31 hcase33 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140b hcase120a hcase120b hcase131a hcase131b hcase320a hcase320b hcase020a hcase020b hcase00 hcase01 hcase03 hcase10 hcase11 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase320b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
        ·
          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140b hcase120a hcase120b hcase131a hcase131b hcase330a hcase330b hcase400a hcase400b hcase420a hcase420b hcase030b hcase020b hcase00 hcase01 hcase04 hcase10 hcase11 hcase30 hcase31 hcase34 hcase41 hcase43 hcase44
                    omega
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase321a hcase330a hcase330b hcase400a hcase400b hcase420a hcase420b hcase030b hcase021a hcase040b hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase34 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase321a hcase321b hcase330a hcase330b hcase400a hcase400b hcase420a hcase420b hcase030a hcase030b hcase021a hcase041a hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase34 hcase41 hcase43 hcase44
                      omega
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                    ·
                      clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase330a hcase330b hcase400b hcase420b hcase031a hcase040b hcase020b hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase34 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase321a hcase321b hcase330a hcase330b hcase400a hcase400b hcase420a hcase420b hcase031a hcase040a hcase040b hcase021a hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase34 hcase41 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase321a hcase321b hcase330a hcase330b hcase400a hcase400b hcase420a hcase420b hcase031a hcase041a hcase00 hcase01 hcase02 hcase10 hcase11 hcase30 hcase31 hcase34 hcase41 hcase43 hcase44
                    omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase321a hcase330b hcase400b hcase421a hcase410b hcase440b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase30 hcase31 hcase34 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase321a hcase330a hcase330b hcase400b hcase421a hcase410b hcase441a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase30 hcase31 hcase34 hcase43
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase321a hcase321b hcase330a hcase330b hcase400a hcase400b hcase421a hcase411a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase30 hcase31 hcase34 hcase43 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100b hcase110b hcase140b hcase120b hcase131a hcase321a hcase321b hcase330a hcase330b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase30 hcase31 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase331a hcase331b hcase040a hcase040b hcase400b hcase420b hcase410b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase30 hcase31 hcase34 hcase43 hcase44
                    omega
                  ·
                    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase321a hcase040b hcase400a hcase400b hcase420a hcase420b hcase411a hcase411b hcase030b hcase00 hcase01 hcase02 hcase10 hcase11 hcase30 hcase31 hcase34 hcase43 hcase44
                      omega
                    ·
                      rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                      ·
                        clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase331a hcase331b hcase040b hcase400b hcase420b hcase411a hcase031a hcase020b hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase34 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase321a hcase321b hcase331a hcase331b hcase040a hcase040b hcase400a hcase400b hcase420a hcase420b hcase411a hcase411b hcase031a hcase021a hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase34 hcase43 hcase44
                        omega
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase321a hcase040b hcase400b hcase421a hcase430b hcase440b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase30 hcase31 hcase34 hcase41
                      omega
                    ·
                      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase321a hcase040b hcase400a hcase400b hcase430a hcase430b hcase441a hcase441b hcase030b hcase00 hcase01 hcase02 hcase10 hcase11 hcase30 hcase31 hcase34 hcase41
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase321a hcase331a hcase331b hcase040b hcase400b hcase421a hcase430a hcase430b hcase441a hcase031a hcase00 hcase01 hcase02 hcase10 hcase11 hcase30 hcase31 hcase34 hcase41
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase120a hcase120b hcase131a hcase131b hcase321a hcase321b hcase331a hcase331b hcase040a hcase040b hcase400a hcase400b hcase421a hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase30 hcase31 hcase34 hcase41 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100b hcase110b hcase140b hcase120b hcase131a hcase321a hcase321b hcase331a hcase331b hcase040a hcase040b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase30 hcase31 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140b hcase120a hcase120b hcase131a hcase131b hcase321a hcase321b hcase331a hcase331b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
    ·
      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
      ·
        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
        ·
          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
          ·
            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  clear hsum_nat1 hsum_nat4 hcut26 hcut30 hcut35 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040b hcase030b hcase020b hcase340b hcase310b hcase300b hcase00 hcase01 hcase10 hcase11 hcase13 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut30 hcut35 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase040b hcase030b hcase020b hcase340b hcase310b hcase301a hcase00 hcase01 hcase10 hcase11 hcase13 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut26 hcut35 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040b hcase030b hcase020b hcase340b hcase311a hcase00 hcase01 hcase10 hcase11 hcase13 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100b hcase110b hcase140b hcase121a hcase040b hcase030b hcase020b hcase130b hcase400b hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100b hcase110b hcase140b hcase121a hcase040a hcase040b hcase030b hcase020b hcase130b hcase401a hcase430b hcase440b hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase41 hcase42
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040b hcase030b hcase020b hcase341a hcase341b hcase130a hcase130b hcase401a hcase401b hcase430a hcase430b hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase41 hcase42
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040a hcase040b hcase030a hcase030b hcase020a hcase020b hcase341a hcase341b hcase130a hcase130b hcase401a hcase431a hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase41 hcase42 hcase44
                    omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase040b hcase030b hcase020b hcase131a hcase131b hcase420a hcase420b hcase400b hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase41 hcase43 hcase44
                    omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040b hcase030b hcase020b hcase341a hcase341b hcase420b hcase401a hcase410b hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040a hcase040b hcase030a hcase030b hcase020a hcase020b hcase341a hcase341b hcase131a hcase131b hcase420a hcase420b hcase401a hcase411a hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040b hcase030b hcase020a hcase020b hcase341a hcase341b hcase131a hcase131b hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase43 hcase44
                  omega
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040a hcase040b hcase030a hcase030b hcase320b hcase00 hcase01 hcase10 hcase11 hcase13 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040b hcase030b hcase021a hcase321a hcase00 hcase01 hcase10 hcase11 hcase13 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040a hcase040b hcase130b hcase00 hcase01 hcase02 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
            ·
              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121b hcase040b hcase031a hcase131a hcase131b hcase430b hcase440b hcase400b hcase00 hcase01 hcase02 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                  omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040a hcase040b hcase131a hcase430b hcase440b hcase401a hcase320b hcase00 hcase01 hcase02 hcase10 hcase11 hcase30 hcase31 hcase33 hcase34 hcase41 hcase42
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040b hcase031a hcase131a hcase430b hcase440b hcase401a hcase321a hcase00 hcase01 hcase02 hcase10 hcase11 hcase30 hcase31 hcase33 hcase34 hcase41 hcase42
                    omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121b hcase040b hcase031a hcase131a hcase131b hcase430a hcase430b hcase441a hcase400b hcase320b hcase00 hcase01 hcase02 hcase10 hcase11 hcase30 hcase31 hcase33 hcase34 hcase41 hcase42
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121b hcase040b hcase031a hcase131a hcase131b hcase430a hcase430b hcase441a hcase400b hcase321a hcase00 hcase01 hcase02 hcase10 hcase11 hcase30 hcase31 hcase33 hcase34 hcase41 hcase42
                    omega
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040b hcase031a hcase131a hcase430a hcase430b hcase441a hcase401a hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040a hcase040b hcase031a hcase031b hcase131a hcase131b hcase430a hcase430b hcase441a hcase441b hcase401a hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040a hcase040b hcase031a hcase131a hcase131b hcase430a hcase430b hcase441a hcase441b hcase401a hcase401b hcase021a hcase00 hcase01 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                    omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121b hcase040b hcase031a hcase131a hcase131b hcase431a hcase400b hcase320b hcase00 hcase01 hcase02 hcase10 hcase11 hcase30 hcase31 hcase33 hcase34 hcase41 hcase42 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121b hcase040b hcase031a hcase131a hcase131b hcase431a hcase400b hcase321a hcase00 hcase01 hcase02 hcase10 hcase11 hcase30 hcase31 hcase33 hcase34 hcase41 hcase42 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140a hcase140b hcase121a hcase121b hcase040a hcase040b hcase031a hcase031b hcase131a hcase131b hcase431a hcase401a hcase00 hcase01 hcase02 hcase10 hcase11 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase44
                omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase140b hcase121a hcase121b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
  ·
    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
    ·
      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
      ·
        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
        ·
          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hsum_nat0 hsum_nat1 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300b hcase440a hcase440b hcase130a hcase130b hcase030a hcase030b hcase330b hcase430a hcase430b hcase320b hcase020a hcase020b hcase310b hcase340b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42
                        omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase130a hcase130b hcase030a hcase030b hcase330a hcase330b hcase430b hcase320a hcase320b hcase020a hcase020b hcase310a hcase310b hcase341b hcase400b hcase410b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase42
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130b hcase030a hcase030b hcase330a hcase330b hcase430a hcase430b hcase320a hcase320b hcase020a hcase020b hcase310a hcase310b hcase341a hcase341b hcase400a hcase400b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase42
                            omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase130a hcase130b hcase030b hcase330a hcase330b hcase430b hcase320a hcase320b hcase020b hcase310a hcase310b hcase401a hcase410b hcase420b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030a hcase030b hcase330a hcase330b hcase430a hcase430b hcase320a hcase320b hcase020a hcase020b hcase310a hcase310b hcase341a hcase341b hcase401a hcase410a hcase410b hcase421a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030a hcase030b hcase330a hcase330b hcase430a hcase430b hcase320a hcase320b hcase020a hcase020b hcase310a hcase310b hcase341a hcase341b hcase401a hcase411a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase42
                            omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut26 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030a hcase030b hcase330b hcase430a hcase430b hcase320b hcase020a hcase020b hcase311a hcase410a hcase410b hcase340b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase40 hcase42
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase130a hcase130b hcase030a hcase030b hcase330a hcase330b hcase430b hcase320a hcase320b hcase020a hcase020b hcase311b hcase410b hcase341b hcase420b hcase400b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase130a hcase130b hcase030b hcase330a hcase330b hcase430b hcase320a hcase320b hcase020b hcase311a hcase311b hcase410b hcase420b hcase401a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030a hcase030b hcase330a hcase330b hcase430a hcase430b hcase320b hcase020a hcase020b hcase311a hcase311b hcase410a hcase410b hcase341a hcase341b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase40
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130b hcase030a hcase030b hcase330a hcase330b hcase430a hcase430b hcase320a hcase320b hcase020a hcase020b hcase311a hcase311b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase34 hcase40 hcase42
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030a hcase030b hcase330a hcase330b hcase430a hcase430b hcase320b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase31 hcase34 hcase40 hcase41 hcase42
                    omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase130a hcase130b hcase030a hcase030b hcase330a hcase330b hcase430b hcase321a hcase410b hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42
                      omega
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase040b hcase020b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030b hcase330a hcase330b hcase430a hcase430b hcase321a hcase410a hcase410b hcase401a hcase401b hcase040b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42
                          omega
                      ·
                        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase130a hcase130b hcase030b hcase330a hcase330b hcase430b hcase410b hcase401a hcase041a hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030a hcase030b hcase330a hcase330b hcase430a hcase430b hcase321a hcase321b hcase410a hcase410b hcase401a hcase041a hcase041b hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030a hcase030b hcase330a hcase330b hcase430a hcase430b hcase321a hcase321b hcase410a hcase410b hcase401a hcase401b hcase041a hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42
                          omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130b hcase030a hcase030b hcase330a hcase330b hcase430a hcase430b hcase321a hcase321b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase34 hcase40 hcase42
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030a hcase030b hcase330b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42
                omega
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase130a hcase130b hcase030a hcase030b hcase331b hcase430b hcase410b hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase34 hcase42
                    omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase320b hcase040b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase130a hcase130b hcase030b hcase430b hcase410b hcase401a hcase320b hcase041a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42
                        omega
                    ·
                      rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase020b hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase130a hcase130b hcase030b hcase430b hcase410b hcase401a hcase321a hcase321b hcase020b hcase041a hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030a hcase030b hcase331a hcase331b hcase430a hcase430b hcase410a hcase410b hcase401a hcase321a hcase321b hcase020a hcase020b hcase041a hcase041b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34
                            omega
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase130a hcase130b hcase030b hcase430b hcase410b hcase401a hcase321a hcase021a hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030a hcase030b hcase331a hcase331b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase321a hcase321b hcase021a hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42
                          omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130b hcase030a hcase030b hcase331a hcase331b hcase430a hcase430b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase34 hcase40 hcase42
                  omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase130a hcase130b hcase030a hcase030b hcase331a hcase431a hcase410b hcase400b hcase320b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut74 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase130a hcase130b hcase030a hcase030b hcase331a hcase431a hcase410b hcase400b hcase321a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030a hcase030b hcase331a hcase331b hcase431a hcase410a hcase410b hcase401a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase34 hcase42
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130a hcase130b hcase030a hcase030b hcase331a hcase331b hcase431a hcase411a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase34 hcase40 hcase42
                  omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase130b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43
            omega
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141b hcase300a hcase300b hcase440a hcase440b hcase131b hcase400b hcase030b hcase040b hcase020b hcase420b hcase410b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141b hcase300a hcase300b hcase440a hcase440b hcase131a hcase131b hcase400b hcase030a hcase030b hcase040b hcase020b hcase420b hcase411a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase43
                      omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase131a hcase131b hcase400a hcase400b hcase030b hcase040b hcase020a hcase020b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43
                    omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase131a hcase131b hcase400a hcase400b hcase030a hcase030b hcase040a hcase040b hcase320b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase131a hcase131b hcase400a hcase400b hcase030b hcase040b hcase021a hcase321a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43
                    omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141b hcase300a hcase300b hcase440b hcase131b hcase400b hcase030a hcase030b hcase041a hcase041b hcase410b hcase320b hcase330b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase131b hcase400b hcase030b hcase041a hcase410b hcase320b hcase331a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42 hcase43
                      omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase131b hcase400b hcase030b hcase041a hcase410b hcase321a hcase330b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut74 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase131b hcase400b hcase030b hcase041a hcase410b hcase321a hcase331a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42 hcase43
                      omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase131a hcase131b hcase400b hcase030a hcase030b hcase411a hcase330b hcase420b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase32 hcase34 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase131a hcase131b hcase400a hcase400b hcase030a hcase030b hcase041a hcase041b hcase411a hcase330a hcase330b hcase421a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase32 hcase34 hcase43
                      omega
                  ·
                    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase131a hcase131b hcase400b hcase030a hcase030b hcase041a hcase411a hcase331a hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase34 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase131a hcase131b hcase400a hcase400b hcase030a hcase030b hcase041a hcase041b hcase411a hcase331a hcase331b hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase34 hcase43
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase131a hcase131b hcase400a hcase400b hcase030a hcase030b hcase041a hcase411a hcase411b hcase331a hcase331b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase34 hcase42 hcase43
                      omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141b hcase300a hcase300b hcase440b hcase131a hcase131b hcase400b hcase320b hcase040a hcase040b hcase330b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase34 hcase41 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141b hcase300a hcase300b hcase440b hcase131a hcase131b hcase400b hcase031a hcase320b hcase040b hcase331a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase34 hcase41 hcase42 hcase43
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase131a hcase131b hcase400a hcase400b hcase031a hcase320a hcase320b hcase041a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43
                  omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141b hcase300a hcase300b hcase440b hcase131a hcase131b hcase400b hcase031a hcase321a hcase040b hcase330b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase34 hcase41 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut74 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141b hcase300a hcase300b hcase440b hcase131a hcase131b hcase400b hcase031a hcase321a hcase040b hcase331a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase34 hcase41 hcase42 hcase43
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase131a hcase131b hcase400a hcase400b hcase031a hcase321a hcase321b hcase041a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43
                  omega
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440b hcase401a hcase410b hcase420b hcase430b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase131a hcase131b hcase401a hcase410a hcase410b hcase420a hcase420b hcase431a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase131a hcase131b hcase401a hcase410a hcase410b hcase421a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase43
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase440a hcase440b hcase131a hcase131b hcase401a hcase411a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43
              omega
      ·
        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase430a hcase430b hcase400a hcase400b hcase020b hcase040b hcase030b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                  omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141b hcase300a hcase300b hcase441a hcase430a hcase430b hcase400b hcase020a hcase020b hcase040b hcase031a hcase320b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141b hcase300a hcase300b hcase441a hcase430a hcase430b hcase400b hcase020a hcase020b hcase040b hcase031a hcase321a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42
                    omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase430a hcase430b hcase400b hcase020a hcase020b hcase041a hcase041b hcase420b hcase410b hcase00 hcase01 hcase03 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase34
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase430a hcase430b hcase400b hcase020b hcase041a hcase420b hcase411a hcase00 hcase01 hcase03 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase34
                    omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase400a hcase400b hcase020a hcase020b hcase041a hcase041b hcase410a hcase410b hcase320b hcase00 hcase01 hcase03 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase430a hcase430b hcase400b hcase020a hcase020b hcase041a hcase041b hcase421a hcase410b hcase321a hcase00 hcase01 hcase03 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase400a hcase400b hcase020a hcase020b hcase041a hcase041b hcase421a hcase411a hcase00 hcase01 hcase03 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase34
                    omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase400a hcase400b hcase320b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42
                omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141b hcase300a hcase300b hcase441a hcase430a hcase430b hcase400b hcase021a hcase321a hcase040b hcase00 hcase01 hcase03 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase400a hcase400b hcase021a hcase321a hcase321b hcase041a hcase00 hcase01 hcase03 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42
                  omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase430a hcase430b hcase401a hcase401b hcase130a hcase130b hcase040b hcase030b hcase020b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                    omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase401a hcase401b hcase130a hcase130b hcase040a hcase040b hcase030a hcase030b hcase320b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase430a hcase430b hcase401a hcase401b hcase130a hcase130b hcase040b hcase030b hcase021a hcase321a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase401a hcase401b hcase130b hcase040a hcase040b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                  omega
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase430b hcase401a hcase130a hcase130b hcase041a hcase030b hcase020b hcase420b hcase410b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase401a hcase130a hcase130b hcase041a hcase041b hcase030a hcase030b hcase020a hcase020b hcase420a hcase420b hcase411a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase401a hcase130a hcase130b hcase041a hcase041b hcase030a hcase030b hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase41
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase401a hcase401b hcase130a hcase130b hcase041a hcase030a hcase030b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase401a hcase401b hcase130a hcase130b hcase041a hcase031a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                  omega
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase430a hcase430b hcase401a hcase401b hcase131a hcase131b hcase030b hcase040b hcase020b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                    omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase430a hcase430b hcase401a hcase401b hcase131a hcase131b hcase030b hcase040b hcase021a hcase320b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase401a hcase401b hcase131a hcase131b hcase030b hcase040b hcase021a hcase321a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42
                      omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase430b hcase401a hcase030b hcase041a hcase410b hcase020b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase42
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase401a hcase401b hcase131a hcase131b hcase030a hcase030b hcase041a hcase410a hcase410b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase42
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase401a hcase131a hcase131b hcase030a hcase030b hcase041a hcase041b hcase411a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase42
                    omega
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase430a hcase430b hcase401a hcase131a hcase031a hcase020b hcase040b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase41
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase401a hcase131a hcase131b hcase031a hcase031b hcase020a hcase020b hcase040a hcase040b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase41
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase401a hcase401b hcase131a hcase131b hcase031a hcase020a hcase020b hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase430a hcase430b hcase401a hcase401b hcase131a hcase131b hcase031a hcase021a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                  omega
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase431a hcase320b hcase410b hcase400b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase431a hcase320a hcase320b hcase410a hcase410b hcase401a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase431a hcase320a hcase320b hcase411a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase40 hcase42
              omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase431a hcase321a hcase400b hcase410b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase431a hcase321a hcase321b hcase400a hcase400b hcase411a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase300a hcase300b hcase441a hcase441b hcase431a hcase321a hcase321b hcase401a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42
              omega
    ·
      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
      ·
        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
        ·
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut26 hcut35 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase030b hcase400a hcase400b hcase040b hcase020b hcase340b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hcut26 hcut35 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase030b hcase400b hcase040b hcase020b hcase341a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400a hcase400b hcase040a hcase040b hcase320b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030b hcase400a hcase400b hcase040b hcase021a hcase321a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase030b hcase400b hcase041a hcase320a hcase320b hcase020b hcase330a hcase330b hcase410b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase34 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400a hcase400b hcase041a hcase041b hcase320b hcase020a hcase020b hcase330a hcase330b hcase410a hcase410b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase34 hcase43 hcase44
                      omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut26 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase030a hcase030b hcase400a hcase400b hcase041a hcase041b hcase320b hcase020a hcase020b hcase330b hcase411a hcase411b hcase340b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase030a hcase030b hcase400a hcase400b hcase041a hcase041b hcase320b hcase020a hcase020b hcase330a hcase330b hcase341a hcase310b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut26 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase030a hcase030b hcase400b hcase041a hcase041b hcase320b hcase020a hcase020b hcase330a hcase330b hcase411a hcase341a hcase311a hcase430b hcase440b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase42
                            omega
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400b hcase041a hcase320a hcase320b hcase020b hcase330a hcase330b hcase411a hcase341a hcase341b hcase311a hcase311b hcase430a hcase430b hcase441a hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400a hcase400b hcase041a hcase041b hcase320a hcase320b hcase020a hcase020b hcase330a hcase330b hcase411a hcase341a hcase341b hcase311a hcase311b hcase430a hcase430b hcase441a hcase441b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400a hcase400b hcase041a hcase041b hcase320a hcase320b hcase020a hcase020b hcase330a hcase330b hcase411a hcase341a hcase341b hcase311a hcase311b hcase431a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase42 hcase44
                          omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase030b hcase400b hcase041a hcase320a hcase320b hcase020b hcase331a hcase331b hcase420b hcase410b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase34 hcase43 hcase44
                      omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase030a hcase030b hcase400b hcase041a hcase041b hcase320a hcase320b hcase020a hcase020b hcase420a hcase420b hcase411a hcase430b hcase440b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase34
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400b hcase041a hcase320a hcase320b hcase020b hcase331a hcase331b hcase420b hcase411a hcase430a hcase430b hcase441a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase34
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400a hcase400b hcase041a hcase041b hcase320a hcase320b hcase020a hcase020b hcase331a hcase331b hcase420a hcase420b hcase411a hcase431a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase34 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400a hcase400b hcase041a hcase041b hcase320b hcase020a hcase020b hcase331a hcase331b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase34 hcase41 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400a hcase400b hcase041a hcase320a hcase320b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase030b hcase400b hcase041a hcase410b hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase030b hcase400b hcase041a hcase321a hcase410b hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400a hcase400b hcase041a hcase321a hcase321b hcase410a hcase410b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400b hcase041a hcase321a hcase411a hcase430b hcase440b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42
                    omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                      ·
                        clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400b hcase041a hcase411a hcase430a hcase430b hcase441a hcase420b hcase020b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400a hcase400b hcase041a hcase321a hcase321b hcase411a hcase411b hcase430a hcase430b hcase441a hcase441b hcase420a hcase420b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400a hcase400b hcase041a hcase041b hcase321a hcase321b hcase411a hcase430a hcase430b hcase441a hcase441b hcase421a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase400a hcase400b hcase041a hcase041b hcase321a hcase321b hcase411a hcase431a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42 hcase44
                  omega
        ·
          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100b hcase110b hcase141a hcase030a hcase030b hcase401a hcase401b hcase440a hcase440b hcase410a hcase410b hcase040a hcase040b hcase020a hcase020b hcase420a hcase420b hcase130b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100b hcase110b hcase141a hcase030b hcase401a hcase440b hcase410b hcase040b hcase020b hcase420b hcase131a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase43
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase440a hcase440b hcase410a hcase410b hcase040a hcase040b hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase34 hcase43
                    omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase401b hcase440a hcase440b hcase410a hcase410b hcase040a hcase040b hcase320b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030b hcase401a hcase401b hcase440a hcase440b hcase410a hcase410b hcase040b hcase021a hcase321a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42 hcase43
                    omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100b hcase110b hcase141a hcase030a hcase030b hcase401a hcase401b hcase440a hcase440b hcase410a hcase410b hcase041a hcase041b hcase320a hcase320b hcase130b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase42 hcase43
                    omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut26 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase030a hcase030b hcase401a hcase401b hcase440a hcase440b hcase410a hcase410b hcase041a hcase041b hcase320b hcase131a hcase131b hcase330b hcase340b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase42 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030b hcase401a hcase440b hcase410b hcase041a hcase320b hcase330b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase42 hcase43
                        omega
                    ·
                      rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030b hcase401a hcase440b hcase410b hcase041a hcase320a hcase320b hcase331a hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase440a hcase440b hcase410a hcase410b hcase041a hcase041b hcase320a hcase320b hcase131a hcase131b hcase331a hcase331b hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34 hcase43
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase401b hcase440a hcase440b hcase410a hcase410b hcase041a hcase320a hcase320b hcase131a hcase131b hcase331a hcase331b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42 hcase43
                        omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100b hcase110b hcase141a hcase030a hcase030b hcase401a hcase401b hcase440a hcase440b hcase410a hcase410b hcase041a hcase041b hcase321a hcase321b hcase130b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase42 hcase43
                    omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                          ·
                            clear hn4 hsum_nat4 hcut30 hcut35 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100b hcase110b hcase141a hcase301a hcase030b hcase440a hcase440b hcase410a hcase410b hcase041a hcase321a hcase131a hcase330b hcase020b hcase310b hcase340b hcase00 hcase01 hcase10 hcase11 hcase12 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hcut30 hcut35 hcut63 hcut44 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100b hcase110b hcase141a hcase301a hcase030b hcase440b hcase410b hcase041a hcase321a hcase131a hcase330b hcase020b hcase310b hcase341a hcase00 hcase01 hcase10 hcase11 hcase12 hcase42 hcase43
                            omega
                        ·
                          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              clear hn4 hsum_nat1 hcut26 hcut35 hcut63 hcut13 hcut44 hcut69 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase030b hcase401a hcase440b hcase410b hcase041a hcase321a hcase330b hcase020b hcase311a hcase340b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase43
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase440a hcase440b hcase410a hcase410b hcase041a hcase041b hcase321a hcase321b hcase131a hcase131b hcase330a hcase330b hcase020a hcase020b hcase311a hcase311b hcase340a hcase340b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase43
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase030a hcase030b hcase401a hcase401b hcase440a hcase440b hcase410a hcase410b hcase041a hcase041b hcase321a hcase131a hcase131b hcase330a hcase330b hcase020a hcase020b hcase311a hcase341a hcase00 hcase01 hcase10 hcase11 hcase12 hcase42 hcase43
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase401b hcase440a hcase440b hcase410a hcase410b hcase041a hcase321a hcase321b hcase131a hcase131b hcase330a hcase330b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42 hcase43
                        omega
                    ·
                      rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut74 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030b hcase401a hcase440b hcase410b hcase041a hcase331a hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase440a hcase440b hcase410a hcase410b hcase041a hcase041b hcase321a hcase321b hcase131a hcase131b hcase331a hcase331b hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34 hcase43
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase401b hcase440a hcase440b hcase410a hcase410b hcase041a hcase321a hcase321b hcase131a hcase131b hcase331a hcase331b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase34 hcase42 hcase43
                        omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase440a hcase440b hcase411a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43
              omega
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030b hcase401a hcase401b hcase320a hcase320b hcase020b hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43
                  omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100b hcase110b hcase141a hcase030a hcase030b hcase401a hcase401b hcase441a hcase441b hcase320a hcase320b hcase020a hcase020b hcase041a hcase041b hcase420a hcase420b hcase410a hcase410b hcase130b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100b hcase110b hcase141a hcase030b hcase401a hcase441a hcase320a hcase320b hcase020b hcase041a hcase420b hcase410b hcase131a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase43
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase441a hcase441b hcase320a hcase320b hcase020a hcase020b hcase041a hcase041b hcase420a hcase420b hcase411a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase43
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase441a hcase441b hcase320a hcase320b hcase020a hcase020b hcase041a hcase041b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase41 hcase43
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase401b hcase441a hcase441b hcase320b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43
                omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100b hcase110b hcase141a hcase030a hcase030b hcase401a hcase401b hcase441a hcase441b hcase321a hcase321b hcase130b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43
                omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030b hcase401a hcase401b hcase131a hcase131b hcase430a hcase430b hcase040b hcase020b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030b hcase401a hcase401b hcase321a hcase131a hcase131b hcase430a hcase430b hcase040b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42
                      omega
                  ·
                    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030b hcase401a hcase441a hcase321a hcase321b hcase430b hcase041a hcase020b hcase410b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase441a hcase441b hcase321a hcase321b hcase131a hcase131b hcase430a hcase430b hcase041a hcase041b hcase020a hcase020b hcase411a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase42
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase401b hcase441a hcase441b hcase321a hcase321b hcase131a hcase131b hcase430a hcase430b hcase041a hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase030a hcase030b hcase401a hcase441a hcase441b hcase321a hcase321b hcase131a hcase131b hcase431a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42
                  omega
      ·
        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141b hcase301a hcase301b hcase031a hcase410a hcase410b hcase400b hcase040b hcase020b hcase320a hcase320b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase031b hcase410a hcase410b hcase400a hcase400b hcase040a hcase040b hcase020a hcase020b hcase320b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase43 hcase44
                    omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141b hcase301a hcase301b hcase031a hcase410a hcase410b hcase400b hcase040b hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141b hcase301a hcase301b hcase031a hcase410a hcase410b hcase400b hcase040b hcase020a hcase020b hcase321a hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase410a hcase410b hcase400a hcase400b hcase040a hcase040b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase410a hcase410b hcase400a hcase400b hcase041a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100b hcase110b hcase141a hcase031a hcase031b hcase410a hcase410b hcase401a hcase401b hcase130b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase031b hcase410b hcase401a hcase320b hcase430b hcase440b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase42
                    omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase410a hcase410b hcase401a hcase131a hcase320a hcase320b hcase430a hcase430b hcase441a hcase420b hcase020b hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase410a hcase410b hcase401a hcase401b hcase131a hcase131b hcase320a hcase320b hcase430a hcase430b hcase441a hcase441b hcase420a hcase420b hcase020a hcase020b hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase410a hcase410b hcase401a hcase401b hcase131a hcase131b hcase320a hcase320b hcase430a hcase430b hcase441a hcase441b hcase420a hcase420b hcase021a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase031b hcase410a hcase410b hcase401a hcase131a hcase131b hcase320a hcase320b hcase430a hcase430b hcase441a hcase441b hcase421a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase031b hcase410a hcase410b hcase401a hcase131a hcase131b hcase320a hcase320b hcase431a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase42 hcase44
                  omega
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase410a hcase410b hcase401a hcase131a hcase020b hcase420b hcase430b hcase440b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34
                        omega
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase410a hcase410b hcase401a hcase131a hcase020b hcase420b hcase430a hcase430b hcase441a hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase410a hcase410b hcase401a hcase401b hcase131a hcase131b hcase321a hcase321b hcase020a hcase020b hcase420a hcase420b hcase430a hcase430b hcase441a hcase441b hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase031b hcase410a hcase410b hcase401a hcase131a hcase131b hcase321a hcase321b hcase020a hcase020b hcase420a hcase420b hcase431a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase031b hcase410a hcase410b hcase401a hcase131a hcase131b hcase321a hcase321b hcase020a hcase020b hcase421a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase410a hcase410b hcase401a hcase401b hcase131a hcase131b hcase321a hcase321b hcase021a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141b hcase301a hcase301b hcase031a hcase411a hcase320b hcase400b hcase040b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase411a hcase411b hcase320a hcase320b hcase400a hcase400b hcase041a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase031b hcase411a hcase320a hcase320b hcase401a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                clear hn4 hsum_nat3 hcut26 hcut30 hcut35 hcut31 hcut63 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase001a hcase100a hcase100b hcase110a hcase110b hcase141b hcase301a hcase301b hcase031a hcase411a hcase321a hcase400b hcase040b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase411a hcase411b hcase321a hcase321b hcase400a hcase400b hcase041a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut26 hcut30 hcut35 hcut31 hcut63 hcut13 hcut44 hcut69 hcut12 hcut74 hcut64 hcut71 hcut65 hcut23 hcut58 hcut2 hcut53 hcut48 hcut6 hcut21 hcut59 hcut3 hcut51 hcut72 hcut38 hcut56 hcut5 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase001a hcase001b hcase100a hcase100b hcase110a hcase110b hcase141a hcase141b hcase301a hcase301b hcase031a hcase031b hcase411a hcase321a hcase321b hcase401a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
              omega

#print axioms symbolic_v2_mask519_integer_shard001
end Jsp404.SixExactFloorKernel
