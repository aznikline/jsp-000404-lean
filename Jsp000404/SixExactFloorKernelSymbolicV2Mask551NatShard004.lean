import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask551_integer_shard004 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut5 : (s02 + s42 + u02 + u42) + 1 ≤ (s32 + 2))
    (hcut15 : (s13 + s40 + u13 + u40) + 1 ≤ (n))
    (hcut36 : (s43 + u43 + 1) + 1 ≤ (n))
    (hcut28 : (s33 + u33 + 2) + 1 ≤ (n))
    (hcut2 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 1))
    (hcut23 : (s01 + s03 + s04 + s40 + s44 + u01 + u03 + u04 + u40 + u44) + 1 ≤ (2 * n))
    (hcut12 : (s30 + u30 + 2) + 1 ≤ (n))
    (hcut26 : (s03 + s11 + s14 + s31 + u03 + u11 + u14 + u31 + 1) + 1 ≤ (n))
    (hcut32 : (s30 + s33 + s34 + u30 + u33 + u34 + 1) + 1 ≤ (n))
    (hcut43 : (s03 + s10 + s11 + s14 + s31 + s32 + u03 + u10 + u11 + u14 + u31 + u32) + 1 ≤ (n + 1))
    (hcut3 : (s03 + s32 + s41 + u03 + u32 + u41) + 1 ≤ (s13 + 2))
    (hcut18 : (s12 + u12) + 1 ≤ (s31 + 2))
    (hcut11 : (s11 + s31 + u11 + u31 + 2) + 1 ≤ (n))
    (hcut4 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut9 : (s40 + s41 + s42 + s43 + u40 + u41 + u42 + u43) + 1 ≤ (n))
    (hcut33 : (s12 + s13 + s14 + s30 + u12 + u13 + u14 + u30) + 1 ≤ (n + 1))
    (hcut35 : (s03 + s10 + s11 + s14 + s31 + u03 + u10 + u11 + u14 + u31) + 1 ≤ (n))
    (hcut29 : (s00 + s04 + s40 + s44 + u00 + u04 + u40 + u44) + 1 ≤ (2 * n))
    (hcut38 : (s00 + s04 + s34 + s43 + u00 + u04 + u34 + u43) + 1 ≤ (2 * n))
    (hcut46 : (s00 + s01 + s43 + s44 + u00 + u01 + u43 + u44) + 1 ≤ (n + 2))
    (hcut45 : (s01 + s43 + s44 + u01 + u43 + u44) + 1 ≤ (n + 1))
    (hcut16 : (s10 + s11 + s31 + u10 + u11 + u31 + 1) + 1 ≤ (n))
    (hcut1 : (s32 + s33 + s34 + s40 + s41 + u32 + u33 + u34 + u40 + u41) + 1 ≤ (n + 1))
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
    (hcase020a : s02 = 0)
    (hcase020b : u02 = 0)
    (hcase031a : 1 ≤ s03)
    (hcase031b : u03 = 1)
    : False := by
  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
  ·
    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
    ·
      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
      ·
        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            clear hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100b hcase120b hcase110b hcase140b hcase130b hcase00 hcase01 hcase02 hcase03 hcase04 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400a hcase400b hcase420a hcase420b hcase010b hcase000b hcase040b hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400a hcase400b hcase420a hcase420b hcase010a hcase010b hcase000a hcase000b hcase041a hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43 hcase44
                      omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400b hcase420b hcase010a hcase010b hcase001a hcase001b hcase440b hcase430b hcase02 hcase03 hcase04 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41
                        omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400b hcase420b hcase010a hcase010b hcase001a hcase001b hcase440b hcase431a hcase410b hcase02 hcase03 hcase04 hcase30 hcase31 hcase32 hcase33 hcase34
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400a hcase400b hcase420a hcase420b hcase010a hcase010b hcase001a hcase001b hcase440a hcase440b hcase431a hcase411a hcase02 hcase03 hcase04 hcase30 hcase31 hcase32 hcase33 hcase34
                          omega
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400b hcase420b hcase010a hcase010b hcase441a hcase040a hcase040b hcase410b hcase430b hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400b hcase420b hcase010a hcase010b hcase441a hcase040a hcase040b hcase410b hcase431a hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34
                            omega
                        ·
                          clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400b hcase420b hcase010a hcase010b hcase001a hcase441a hcase040b hcase411a hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase43
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400a hcase400b hcase420a hcase420b hcase010a hcase010b hcase001a hcase001b hcase441a hcase441b hcase041a hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43
                        omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400a hcase400b hcase420a hcase420b hcase011a hcase00 hcase02 hcase03 hcase04 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43 hcase44
                  omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400a hcase400b hcase040a hcase040b hcase320b hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase33 hcase34 hcase41 hcase43 hcase44
                    omega
                  ·
                    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                        ·
                          clear hn4 hsum_nat3 hsum_nat4 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400a hcase400b hcase040b hcase321a hcase010b hcase430a hcase430b hcase000b hcase02 hcase03 hcase30 hcase31 hcase33 hcase34 hcase41 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400b hcase421a hcase040b hcase321a hcase010b hcase430b hcase001a hcase02 hcase03 hcase30 hcase31 hcase33 hcase34 hcase41 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400a hcase400b hcase421a hcase040a hcase040b hcase321a hcase321b hcase010a hcase010b hcase431a hcase00 hcase02 hcase03 hcase30 hcase31 hcase33 hcase34 hcase41 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400a hcase400b hcase421a hcase421b hcase040a hcase040b hcase321a hcase321b hcase011a hcase00 hcase02 hcase03 hcase30 hcase31 hcase33 hcase34 hcase41 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase400a hcase400b hcase421a hcase421b hcase041a hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100b hcase120b hcase110b hcase140b hcase131a hcase00 hcase01 hcase02 hcase03 hcase04 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase010b hcase300a hcase300b hcase430a hcase430b hcase400a hcase400b hcase320a hcase320b hcase410a hcase410b hcase000b hcase02 hcase03 hcase04 hcase13 hcase31 hcase33 hcase34 hcase42 hcase44
                        omega
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase010b hcase300a hcase300b hcase430b hcase400b hcase320b hcase410b hcase001a hcase040b hcase02 hcase03 hcase13 hcase31 hcase33 hcase34 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase010a hcase010b hcase300a hcase300b hcase430a hcase430b hcase400a hcase400b hcase320a hcase320b hcase410a hcase410b hcase001a hcase001b hcase041a hcase02 hcase03 hcase13 hcase31 hcase33 hcase34 hcase42 hcase44
                          omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                        ·
                          clear hn4 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase010b hcase300a hcase300b hcase430a hcase430b hcase400a hcase400b hcase320a hcase320b hcase420a hcase420b hcase000b hcase02 hcase03 hcase04 hcase13 hcase31 hcase33 hcase34 hcase44
                          omega
                        ·
                          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                          ·
                            clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141b hcase010b hcase300a hcase300b hcase430b hcase400b hcase320a hcase320b hcase411a hcase420b hcase001a hcase040b hcase02 hcase03 hcase13 hcase31 hcase33 hcase34 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase010a hcase010b hcase300a hcase300b hcase430a hcase430b hcase400a hcase400b hcase320a hcase320b hcase411a hcase411b hcase420a hcase420b hcase001a hcase001b hcase041a hcase02 hcase03 hcase13 hcase31 hcase33 hcase34 hcase44
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase010a hcase010b hcase300a hcase300b hcase430a hcase430b hcase400a hcase400b hcase320a hcase320b hcase411a hcase421a hcase00 hcase02 hcase03 hcase04 hcase13 hcase31 hcase33 hcase34 hcase44
                        omega
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase010b hcase300a hcase300b hcase430a hcase430b hcase400a hcase400b hcase321a hcase321b hcase000b hcase02 hcase03 hcase04 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42 hcase44
                      omega
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141b hcase010b hcase300a hcase300b hcase430b hcase400b hcase321a hcase001a hcase040b hcase02 hcase03 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase010a hcase010b hcase300a hcase300b hcase430a hcase430b hcase400a hcase400b hcase321a hcase321b hcase001a hcase001b hcase041a hcase02 hcase03 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42 hcase44
                        omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase010a hcase010b hcase300b hcase430a hcase430b hcase401a hcase401b hcase330b hcase340b hcase00 hcase02 hcase03 hcase04 hcase13 hcase31 hcase32 hcase41 hcase42 hcase44
                      omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase010b hcase300a hcase300b hcase430a hcase430b hcase401a hcase401b hcase330a hcase330b hcase341a hcase341b hcase420a hcase420b hcase000b hcase02 hcase03 hcase04 hcase13 hcase31 hcase32 hcase41 hcase44
                          omega
                        ·
                          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                          ·
                            clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase010b hcase300b hcase430b hcase401a hcase330a hcase330b hcase341a hcase420b hcase001a hcase040b hcase02 hcase03 hcase13 hcase31 hcase32 hcase41 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase010a hcase010b hcase300a hcase300b hcase430a hcase430b hcase401a hcase401b hcase330a hcase330b hcase341a hcase341b hcase420a hcase420b hcase001a hcase001b hcase041a hcase02 hcase03 hcase13 hcase31 hcase32 hcase41 hcase44
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase010a hcase010b hcase300a hcase300b hcase430a hcase430b hcase401a hcase330a hcase330b hcase341a hcase341b hcase421a hcase00 hcase02 hcase03 hcase04 hcase13 hcase31 hcase32 hcase41 hcase44
                        omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase010b hcase300a hcase300b hcase430a hcase430b hcase401a hcase401b hcase331a hcase331b hcase320a hcase320b hcase000b hcase02 hcase03 hcase04 hcase13 hcase31 hcase34 hcase41 hcase42 hcase44
                        omega
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                          ·
                            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase010a hcase010b hcase300b hcase430a hcase430b hcase401a hcase401b hcase331a hcase320b hcase001a hcase001b hcase040a hcase040b hcase340b hcase310b hcase02 hcase03 hcase13 hcase41 hcase42 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut15 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase010b hcase300b hcase430b hcase401a hcase331a hcase320b hcase001a hcase040b hcase340a hcase340b hcase311a hcase02 hcase03 hcase13 hcase41 hcase42 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat1 hcut15 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase010b hcase300b hcase430b hcase401a hcase331a hcase320b hcase001a hcase040b hcase341a hcase02 hcase03 hcase13 hcase31 hcase41 hcase42 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase010a hcase010b hcase300a hcase300b hcase430a hcase430b hcase401a hcase401b hcase331a hcase331b hcase320a hcase320b hcase001a hcase001b hcase041a hcase02 hcase03 hcase13 hcase31 hcase34 hcase41 hcase42 hcase44
                          omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase010b hcase300b hcase430b hcase401a hcase331a hcase321a hcase420b hcase040b hcase00 hcase02 hcase03 hcase13 hcase31 hcase34 hcase41 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase010a hcase010b hcase300a hcase300b hcase430a hcase430b hcase401a hcase401b hcase331a hcase331b hcase321a hcase321b hcase420a hcase420b hcase041a hcase00 hcase02 hcase03 hcase13 hcase31 hcase34 hcase41 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase010a hcase010b hcase300a hcase300b hcase430a hcase430b hcase401a hcase331a hcase331b hcase321a hcase321b hcase421a hcase00 hcase02 hcase03 hcase04 hcase13 hcase31 hcase34 hcase41 hcase44
                        omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase010b hcase300a hcase300b hcase431a hcase431b hcase040b hcase000b hcase02 hcase03 hcase13 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
                    omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase010a hcase010b hcase300a hcase300b hcase431a hcase040b hcase001a hcase400b hcase320b hcase410b hcase02 hcase03 hcase13 hcase31 hcase33 hcase34 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase010a hcase010b hcase300a hcase300b hcase431a hcase040a hcase040b hcase001a hcase001b hcase400a hcase400b hcase320a hcase320b hcase411a hcase02 hcase03 hcase13 hcase31 hcase33 hcase34 hcase42 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141b hcase010a hcase010b hcase300a hcase300b hcase431a hcase040b hcase001a hcase400b hcase321a hcase02 hcase03 hcase13 hcase31 hcase33 hcase34 hcase41 hcase42 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase010a hcase010b hcase300a hcase300b hcase431a hcase040a hcase040b hcase001a hcase001b hcase401a hcase02 hcase03 hcase13 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase010a hcase010b hcase300a hcase300b hcase431a hcase431b hcase041a hcase00 hcase02 hcase03 hcase13 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
                  omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase100b hcase120b hcase110a hcase110b hcase141a hcase010a hcase010b hcase301a hcase301b hcase130b hcase00 hcase02 hcase03 hcase04 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100b hcase120a hcase120b hcase110b hcase141a hcase010a hcase010b hcase131a hcase00 hcase02 hcase03 hcase04 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase011a hcase00 hcase02 hcase03 hcase04 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
      ·
        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
        ·
          rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase400a hcase400b hcase000b hcase010b hcase02 hcase03 hcase04 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase400a hcase400b hcase000a hcase000b hcase011a hcase02 hcase03 hcase04 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase400b hcase001a hcase040b hcase320a hcase320b hcase410b hcase420b hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase400a hcase400b hcase001a hcase001b hcase040a hcase040b hcase320b hcase410a hcase410b hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase43 hcase44
                    omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase111b hcase400b hcase001a hcase040b hcase320a hcase320b hcase411a hcase420b hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase400a hcase400b hcase001a hcase001b hcase040a hcase040b hcase320a hcase320b hcase411a hcase421a hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase43 hcase44
                    omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase400b hcase001a hcase040b hcase321a hcase321b hcase410b hcase420b hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase111b hcase400b hcase001a hcase040b hcase321a hcase410a hcase410b hcase421a hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase111b hcase400b hcase001a hcase040b hcase321a hcase411a hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase400a hcase400b hcase001a hcase001b hcase041a hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
            ·
              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase401a hcase401b hcase040b hcase000b hcase010b hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase401a hcase401b hcase040a hcase040b hcase000a hcase000b hcase011a hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase100b hcase120b hcase111a hcase401a hcase401b hcase040a hcase040b hcase001a hcase001b hcase130b hcase01 hcase02 hcase03 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase100a hcase100b hcase120a hcase120b hcase401a hcase401b hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase320b hcase330b hcase300b hcase430a hcase430b hcase420a hcase420b hcase340b hcase02 hcase03 hcase14 hcase31 hcase41 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase401a hcase040b hcase001a hcase131a hcase131b hcase010b hcase320a hcase320b hcase330a hcase330b hcase300b hcase430b hcase420b hcase341a hcase02 hcase03 hcase14 hcase31 hcase41 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase401a hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase320a hcase320b hcase330a hcase330b hcase300a hcase300b hcase430a hcase430b hcase421a hcase02 hcase03 hcase14 hcase31 hcase34 hcase41 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase401a hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase320a hcase320b hcase330a hcase330b hcase300a hcase300b hcase431a hcase02 hcase03 hcase14 hcase31 hcase34 hcase41 hcase42 hcase44
                          omega
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase100b hcase120a hcase120b hcase111a hcase401a hcase401b hcase040a hcase040b hcase001a hcase001b hcase131a hcase010a hcase010b hcase320b hcase330b hcase301a hcase340b hcase02 hcase03 hcase14 hcase31 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase401a hcase401b hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase320b hcase330a hcase330b hcase301a hcase341a hcase310b hcase02 hcase03 hcase14 hcase41 hcase42 hcase43 hcase44
                            omega
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              clear hn4 hcut36 hcut28 hcut2 hcut23 hcut12 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase100b hcase120b hcase111a hcase401a hcase040b hcase001a hcase131a hcase010a hcase010b hcase320b hcase330a hcase330b hcase301a hcase341a hcase311a hcase410b hcase02 hcase03 hcase14 hcase42 hcase43 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase401a hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase320a hcase320b hcase330a hcase330b hcase301a hcase301b hcase341a hcase341b hcase311a hcase311b hcase411a hcase02 hcase03 hcase14 hcase42 hcase43 hcase44
                              omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                          ·
                            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase401a hcase401b hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase320b hcase331a hcase410a hcase410b hcase310b hcase300b hcase340b hcase02 hcase03 hcase14 hcase42 hcase43 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase401a hcase401b hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase320b hcase331a hcase410a hcase410b hcase310b hcase300a hcase300b hcase341a hcase02 hcase03 hcase14 hcase42 hcase43 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase401a hcase401b hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase320b hcase331a hcase410a hcase410b hcase310b hcase301a hcase02 hcase03 hcase14 hcase34 hcase42 hcase43 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat3 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase100b hcase120b hcase111a hcase401a hcase040b hcase001a hcase131a hcase010a hcase010b hcase320b hcase331a hcase331b hcase410b hcase02 hcase03 hcase14 hcase30 hcase34 hcase42 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase401a hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase320a hcase320b hcase331a hcase331b hcase411a hcase02 hcase03 hcase14 hcase30 hcase31 hcase34 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase401a hcase040b hcase001a hcase131a hcase010a hcase010b hcase420b hcase02 hcase03 hcase14 hcase30 hcase31 hcase33 hcase34 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase401a hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase321a hcase321b hcase421a hcase02 hcase03 hcase14 hcase30 hcase31 hcase33 hcase34 hcase41 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase401a hcase401b hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase011a hcase02 hcase03 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                  omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase401a hcase401b hcase041a hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
            omega
    ·
      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
      ·
        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase320a hcase320b hcase310b hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase13 hcase14 hcase30 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase100b hcase121a hcase320a hcase320b hcase311a hcase130b hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase14 hcase30 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase320a hcase320b hcase311a hcase131a hcase131b hcase410a hcase410b hcase400a hcase400b hcase010b hcase000b hcase02 hcase03 hcase04 hcase11 hcase14 hcase30 hcase33 hcase34 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase320a hcase320b hcase311a hcase131a hcase131b hcase410b hcase400b hcase010a hcase010b hcase001a hcase040b hcase420b hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase121a hcase121b hcase320b hcase311a hcase311b hcase131a hcase131b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase001a hcase001b hcase040a hcase040b hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase121a hcase121b hcase320a hcase320b hcase311a hcase311b hcase131a hcase131b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase001a hcase001b hcase041a hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase42 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase121a hcase121b hcase320a hcase320b hcase311a hcase311b hcase131a hcase131b hcase410a hcase410b hcase400a hcase400b hcase011a hcase00 hcase02 hcase03 hcase04 hcase11 hcase14 hcase30 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                    ·
                      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase320a hcase320b hcase311a hcase131a hcase131b hcase410a hcase410b hcase401a hcase401b hcase040b hcase420a hcase420b hcase010b hcase000b hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase43 hcase44
                        omega
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          clear hn4 hsum_nat3 hcut5 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100b hcase121a hcase320a hcase320b hcase311a hcase131a hcase410b hcase401a hcase040b hcase420b hcase010b hcase001a hcase430b hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase121a hcase121b hcase320a hcase320b hcase311a hcase311b hcase131a hcase131b hcase410a hcase410b hcase401a hcase040a hcase040b hcase420a hcase420b hcase010a hcase010b hcase001a hcase001b hcase431a hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase44
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase121a hcase121b hcase320a hcase320b hcase311a hcase311b hcase131a hcase131b hcase410a hcase410b hcase401a hcase401b hcase040a hcase040b hcase420a hcase420b hcase011a hcase00 hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase121a hcase121b hcase320a hcase320b hcase311a hcase311b hcase131a hcase131b hcase410a hcase410b hcase401a hcase040a hcase040b hcase421a hcase00 hcase01 hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase121a hcase121b hcase320a hcase320b hcase311a hcase311b hcase131a hcase131b hcase410a hcase410b hcase401a hcase401b hcase041a hcase00 hcase01 hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase320a hcase320b hcase311a hcase131a hcase131b hcase411a hcase411b hcase040b hcase010b hcase400a hcase400b hcase000b hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase121b hcase320a hcase320b hcase311a hcase311b hcase131a hcase131b hcase411a hcase040b hcase010a hcase010b hcase400b hcase001a hcase420b hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase121a hcase121b hcase320a hcase320b hcase311a hcase311b hcase131a hcase131b hcase411a hcase040a hcase040b hcase010a hcase010b hcase400a hcase400b hcase001a hcase001b hcase421a hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase43 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase121a hcase121b hcase320a hcase320b hcase311a hcase311b hcase131a hcase131b hcase411a hcase040a hcase040b hcase010a hcase010b hcase401a hcase00 hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase121a hcase121b hcase320a hcase320b hcase311a hcase311b hcase131a hcase131b hcase411a hcase411b hcase040a hcase040b hcase011a hcase00 hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase121a hcase121b hcase320a hcase320b hcase311a hcase311b hcase131a hcase131b hcase411a hcase411b hcase041a hcase00 hcase01 hcase02 hcase03 hcase11 hcase14 hcase30 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                omega
      ·
        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
        ·
          rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              clear hn4 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase121b hcase040b hcase000b hcase010b hcase02 hcase03 hcase11 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase121a hcase121b hcase321a hcase321b hcase040a hcase040b hcase000a hcase000b hcase011a hcase02 hcase03 hcase11 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase121b hcase321a hcase040b hcase001a hcase010b hcase430b hcase400b hcase02 hcase03 hcase11 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase41 hcase42 hcase44
                  omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase121a hcase121b hcase040b hcase001a hcase010b hcase430b hcase401a hcase420b hcase02 hcase03 hcase11 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase41 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase121a hcase121b hcase321a hcase321b hcase040a hcase040b hcase001a hcase001b hcase010a hcase010b hcase430a hcase430b hcase401a hcase421a hcase02 hcase03 hcase11 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase41 hcase44
                    omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase100a hcase100b hcase121a hcase121b hcase040a hcase040b hcase001a hcase001b hcase010a hcase010b hcase431a hcase431b hcase420a hcase420b hcase130b hcase02 hcase03 hcase11 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase100a hcase100b hcase121a hcase121b hcase040b hcase001a hcase010a hcase010b hcase431a hcase420b hcase131a hcase02 hcase03 hcase11 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase121a hcase121b hcase321a hcase321b hcase040a hcase040b hcase001a hcase001b hcase010a hcase010b hcase431a hcase421a hcase02 hcase03 hcase11 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase121a hcase121b hcase321a hcase321b hcase040a hcase040b hcase001a hcase001b hcase011a hcase02 hcase03 hcase11 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase100a hcase100b hcase121a hcase121b hcase321a hcase321b hcase041a hcase00 hcase01 hcase02 hcase03 hcase11 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
  ·
    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
    ·
      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
      ·
        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase400a hcase400b hcase410a hcase410b hcase000b hcase010b hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase400a hcase400b hcase410a hcase410b hcase000a hcase000b hcase011a hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase101a hcase101b hcase300b hcase320b hcase340b hcase400a hcase400b hcase410a hcase410b hcase001a hcase001b hcase040a hcase040b hcase330b hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300b hcase320b hcase340b hcase400a hcase400b hcase410a hcase410b hcase001a hcase001b hcase040a hcase040b hcase331a hcase310b hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut15 hcut36 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase300b hcase320b hcase340b hcase400b hcase410b hcase001a hcase040b hcase331a hcase311a hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase42 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase400a hcase400b hcase410a hcase410b hcase001a hcase001b hcase041a hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                ·
                  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                  ·
                    clear hn4 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase400a hcase400b hcase040b hcase000b hcase010b hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase400a hcase400b hcase411a hcase411b hcase040a hcase040b hcase000a hcase000b hcase011a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase400b hcase411a hcase040b hcase001a hcase420b hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase400a hcase400b hcase411a hcase040a hcase040b hcase001a hcase001b hcase421a hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase400a hcase400b hcase411a hcase411b hcase041a hcase00 hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase300b hcase320b hcase340b hcase401a hcase401b hcase330b hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300b hcase320b hcase340b hcase401a hcase401b hcase331a hcase010a hcase010b hcase040a hcase040b hcase310b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase401a hcase401b hcase331a hcase331b hcase010b hcase040b hcase000b hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase401a hcase401b hcase331a hcase331b hcase010a hcase010b hcase040a hcase040b hcase311a hcase311b hcase001a hcase001b hcase420a hcase420b hcase410a hcase410b hcase130b hcase02 hcase03 hcase11 hcase12 hcase14 hcase43 hcase44
                            omega
                          ·
                            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                            ·
                              clear hn4 hsum_nat3 hcut5 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101a hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase401a hcase331a hcase331b hcase010a hcase010b hcase040b hcase001a hcase420b hcase410b hcase131a hcase120b hcase02 hcase03 hcase11 hcase14 hcase43 hcase44
                              omega
                            ·
                              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                              ·
                                clear hn4 hsum_nat3 hcut5 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101a hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase401a hcase331a hcase331b hcase010b hcase040b hcase311a hcase001a hcase420b hcase410b hcase131a hcase121a hcase430b hcase02 hcase03 hcase11 hcase14 hcase44
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase401a hcase331a hcase331b hcase010a hcase010b hcase040a hcase040b hcase311a hcase311b hcase001a hcase001b hcase420a hcase420b hcase410a hcase410b hcase131a hcase131b hcase121a hcase121b hcase431a hcase02 hcase03 hcase11 hcase14 hcase44
                                omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase401a hcase331a hcase331b hcase010a hcase010b hcase040a hcase040b hcase311a hcase311b hcase001a hcase001b hcase420a hcase420b hcase411a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase401a hcase331a hcase331b hcase010a hcase010b hcase040a hcase040b hcase311a hcase311b hcase001a hcase001b hcase421a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase41 hcase43 hcase44
                        omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase401a hcase401b hcase331a hcase331b hcase010a hcase010b hcase041a hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase340a hcase340b hcase401a hcase401b hcase331a hcase331b hcase011a hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase400a hcase400b hcase040b hcase420a hcase420b hcase010b hcase430a hcase430b hcase000b hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase41 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase400b hcase040b hcase420b hcase010b hcase430b hcase001a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase41 hcase44
                      omega
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase400a hcase400b hcase040b hcase420a hcase420b hcase010b hcase431a hcase431b hcase000b hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase41 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase400b hcase040b hcase420b hcase010a hcase010b hcase431a hcase001a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase41 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase400a hcase400b hcase040a hcase040b hcase420a hcase420b hcase011a hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase41 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300a hcase300b hcase320b hcase341a hcase341b hcase400a hcase400b hcase040a hcase040b hcase00 hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase41 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase400a hcase400b hcase041a hcase00 hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hsum_nat0 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300b hcase320a hcase320b hcase341a hcase401a hcase310b hcase420b hcase440b hcase430b hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase401a hcase310a hcase310b hcase420a hcase420b hcase440a hcase440b hcase431a hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41
                    omega
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        clear hn4 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase401a hcase401b hcase310a hcase310b hcase420a hcase420b hcase441a hcase441b hcase040b hcase000b hcase010b hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase401a hcase401b hcase310a hcase310b hcase420a hcase420b hcase441a hcase441b hcase040a hcase040b hcase000a hcase000b hcase011a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41 hcase43
                        omega
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          clear hn4 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase300b hcase320a hcase320b hcase341a hcase401a hcase310b hcase420b hcase441a hcase040b hcase001a hcase010b hcase430b hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase401a hcase310a hcase310b hcase420a hcase420b hcase441a hcase441b hcase040a hcase040b hcase001a hcase001b hcase010a hcase010b hcase431a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase401a hcase401b hcase310a hcase310b hcase420a hcase420b hcase441a hcase441b hcase040a hcase040b hcase001a hcase001b hcase011a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41 hcase43
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase401a hcase401b hcase310a hcase310b hcase420a hcase420b hcase441a hcase441b hcase041a hcase00 hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41 hcase43
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase401a hcase310a hcase310b hcase421a hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41 hcase43 hcase44
                omega
            ·
              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase401a hcase401b hcase010b hcase040b hcase000b hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase300b hcase320a hcase320b hcase341a hcase401a hcase311a hcase010b hcase040b hcase001a hcase420b hcase430b hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase401a hcase311a hcase311b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase420a hcase420b hcase431a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase401a hcase311a hcase311b hcase010a hcase010b hcase040a hcase040b hcase001a hcase001b hcase421a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase401a hcase401b hcase311a hcase311b hcase010a hcase010b hcase041a hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase401a hcase401b hcase311a hcase311b hcase011a hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase33 hcase41 hcase42 hcase43 hcase44
                omega
      ·
        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
        ·
          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase300b hcase321a hcase330b hcase340b hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase400a hcase400b hcase010b hcase420a hcase420b hcase000b hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase400b hcase010a hcase010b hcase420b hcase001a hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase41 hcase43 hcase44
                      omega
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                      ·
                        clear hn4 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase400a hcase400b hcase010b hcase421a hcase421b hcase040b hcase000b hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase41 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase101b hcase300a hcase300b hcase321a hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase400b hcase010a hcase010b hcase421a hcase040b hcase001a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase41 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase321a hcase321b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase400a hcase400b hcase010a hcase010b hcase421a hcase421b hcase041a hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase41 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase321a hcase321b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase400a hcase400b hcase011a hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300b hcase321a hcase330a hcase330b hcase341a hcase310b hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase040b hcase400a hcase400b hcase000b hcase010b hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase321a hcase321b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase040a hcase040b hcase400a hcase400b hcase000a hcase000b hcase011a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase300a hcase300b hcase321a hcase330a hcase330b hcase341a hcase341b hcase040b hcase400b hcase001a hcase410b hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase101b hcase300a hcase300b hcase321a hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase040b hcase400b hcase001a hcase411a hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase300a hcase300b hcase330a hcase330b hcase341a hcase341b hcase040b hcase401a hcase401b hcase010b hcase000b hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase300b hcase330a hcase330b hcase341a hcase311a hcase040b hcase401a hcase010a hcase010b hcase001a hcase420b hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase41 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300a hcase300b hcase321a hcase321b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase040a hcase040b hcase401a hcase010a hcase010b hcase001a hcase001b hcase421a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase41 hcase43 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase321a hcase321b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase040a hcase040b hcase401a hcase401b hcase011a hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase321a hcase321b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase041a hcase00 hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase300a hcase300b hcase331a hcase331b hcase000b hcase010b hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase321a hcase321b hcase331a hcase331b hcase000a hcase000b hcase011a hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase300a hcase300b hcase331a hcase331b hcase001a hcase400b hcase410b hcase040b hcase420b hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase101b hcase300a hcase300b hcase321a hcase331a hcase331b hcase001a hcase400b hcase410a hcase410b hcase040b hcase421a hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase321a hcase321b hcase331a hcase331b hcase001a hcase001b hcase400a hcase400b hcase410a hcase410b hcase041a hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase101b hcase300a hcase300b hcase321a hcase331a hcase331b hcase001a hcase400b hcase411a hcase040b hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase321a hcase321b hcase331a hcase331b hcase001a hcase001b hcase400a hcase400b hcase411a hcase411b hcase041a hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300b hcase321a hcase331a hcase001a hcase001b hcase040a hcase040b hcase310b hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase34 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase300b hcase331a hcase001a hcase401a hcase040b hcase311a hcase420b hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase34 hcase41 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase300a hcase300b hcase321a hcase321b hcase331a hcase331b hcase001a hcase001b hcase401a hcase040a hcase040b hcase311a hcase311b hcase421a hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase34 hcase41 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase300a hcase300b hcase321a hcase321b hcase331a hcase331b hcase001a hcase001b hcase401a hcase401b hcase041a hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
    ·
      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
      ·
        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
        ·
          rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
              ·
                clear hn4 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase301a hcase301b hcase340a hcase340b hcase400a hcase400b hcase000b hcase040b hcase010b hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase400a hcase400b hcase000a hcase000b hcase040a hcase040b hcase011a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase400a hcase400b hcase000a hcase000b hcase041a hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase400a hcase400b hcase001a hcase001b hcase330a hcase330b hcase130b hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase14 hcase31 hcase32 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase340b hcase400a hcase400b hcase001a hcase001b hcase330b hcase131a hcase131b hcase320b hcase310b hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase14 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase101a hcase301a hcase340b hcase400a hcase400b hcase001a hcase001b hcase330b hcase131a hcase320b hcase311a hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase14 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase101a hcase101b hcase301a hcase340b hcase400a hcase400b hcase001a hcase001b hcase330b hcase131a hcase321a hcase310b hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase14 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut4 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase101a hcase301a hcase340b hcase400a hcase400b hcase001a hcase001b hcase330b hcase131a hcase321a hcase311a hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase14 hcase41 hcase42 hcase43 hcase44
                    omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase301a hcase340a hcase340b hcase400b hcase001a hcase331a hcase420b hcase040b hcase310b hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase32 hcase41 hcase43 hcase44
                    omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase301a hcase340a hcase340b hcase400b hcase001a hcase331a hcase420b hcase040b hcase311a hcase410b hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase32 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase301a hcase301b hcase340a hcase340b hcase400b hcase001a hcase331a hcase331b hcase420b hcase040b hcase311a hcase311b hcase411a hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase32 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase400a hcase400b hcase001a hcase001b hcase331a hcase331b hcase420a hcase420b hcase041a hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase41 hcase43 hcase44
                  omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase400a hcase400b hcase001a hcase001b hcase331a hcase331b hcase040a hcase040b hcase320b hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase41 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase101b hcase301a hcase301b hcase340a hcase340b hcase400b hcase001a hcase331a hcase331b hcase421a hcase040b hcase321a hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase41 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase400a hcase400b hcase001a hcase001b hcase331a hcase331b hcase421a hcase421b hcase041a hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase41 hcase43 hcase44
                  omega
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase101a hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase320a hcase320b hcase410a hcase410b hcase120b hcase130b hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase320a hcase320b hcase410a hcase410b hcase120a hcase120b hcase131a hcase131b hcase040b hcase000b hcase010b hcase02 hcase03 hcase11 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase320a hcase320b hcase410a hcase410b hcase120a hcase120b hcase131a hcase131b hcase040a hcase040b hcase000a hcase000b hcase011a hcase02 hcase03 hcase11 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase340b hcase401a hcase401b hcase320b hcase410a hcase410b hcase120a hcase120b hcase131a hcase131b hcase040a hcase040b hcase001a hcase001b hcase420a hcase420b hcase330b hcase310b hcase01 hcase02 hcase03 hcase11 hcase14 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase101a hcase301a hcase340b hcase401a hcase401b hcase320b hcase410a hcase410b hcase120a hcase120b hcase131a hcase040a hcase040b hcase001a hcase001b hcase420a hcase420b hcase330b hcase311a hcase01 hcase02 hcase03 hcase11 hcase14 hcase43 hcase44
                            omega
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase340a hcase340b hcase401a hcase401b hcase320b hcase410a hcase410b hcase120a hcase120b hcase131a hcase131b hcase040a hcase040b hcase001a hcase001b hcase420a hcase420b hcase331a hcase310b hcase01 hcase02 hcase03 hcase11 hcase14 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hcut5 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101a hcase301a hcase340a hcase340b hcase401a hcase320b hcase410b hcase120b hcase131a hcase040b hcase001a hcase420b hcase331a hcase311a hcase01 hcase02 hcase03 hcase11 hcase14 hcase43 hcase44
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase320a hcase320b hcase410a hcase410b hcase120a hcase120b hcase131a hcase131b hcase040a hcase040b hcase001a hcase001b hcase421a hcase01 hcase02 hcase03 hcase11 hcase14 hcase31 hcase33 hcase43 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase320a hcase320b hcase410a hcase410b hcase120a hcase120b hcase131a hcase131b hcase041a hcase00 hcase01 hcase02 hcase03 hcase11 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase320a hcase320b hcase410a hcase410b hcase121a hcase121b hcase040b hcase000b hcase010b hcase02 hcase03 hcase11 hcase13 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase320a hcase320b hcase410a hcase410b hcase121a hcase121b hcase040a hcase040b hcase000a hcase000b hcase011a hcase02 hcase03 hcase11 hcase13 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase101a hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase320a hcase320b hcase410a hcase410b hcase121a hcase040a hcase040b hcase001a hcase001b hcase420a hcase420b hcase010a hcase010b hcase430a hcase430b hcase130b hcase02 hcase03 hcase11 hcase14 hcase31 hcase33 hcase44
                            omega
                          ·
                            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase320a hcase320b hcase410a hcase410b hcase040a hcase040b hcase001a hcase001b hcase420a hcase420b hcase010a hcase010b hcase430a hcase430b hcase131a hcase131b hcase310b hcase02 hcase03 hcase11 hcase14 hcase33 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat3 hcut5 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101a hcase301a hcase301b hcase340a hcase340b hcase401a hcase320a hcase320b hcase410b hcase121a hcase040b hcase001a hcase420b hcase010b hcase430b hcase131a hcase311a hcase02 hcase03 hcase11 hcase14 hcase33 hcase44
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase320a hcase320b hcase410a hcase410b hcase121a hcase121b hcase040a hcase040b hcase001a hcase001b hcase420a hcase420b hcase010a hcase010b hcase431a hcase02 hcase03 hcase11 hcase13 hcase14 hcase31 hcase33 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase320a hcase320b hcase410a hcase410b hcase121a hcase121b hcase040a hcase040b hcase001a hcase001b hcase420a hcase420b hcase011a hcase02 hcase03 hcase11 hcase13 hcase14 hcase31 hcase33 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase320a hcase320b hcase410a hcase410b hcase121a hcase121b hcase040a hcase040b hcase001a hcase001b hcase421a hcase01 hcase02 hcase03 hcase11 hcase13 hcase14 hcase31 hcase33 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase320a hcase320b hcase410a hcase410b hcase121a hcase121b hcase041a hcase00 hcase01 hcase02 hcase03 hcase11 hcase13 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase320a hcase320b hcase411a hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase010b hcase000b hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase010a hcase010b hcase001a hcase001b hcase040a hcase040b hcase130b hcase02 hcase03 hcase11 hcase12 hcase14 hcase31 hcase33 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase010a hcase010b hcase001a hcase040b hcase131a hcase420b hcase02 hcase03 hcase11 hcase12 hcase14 hcase31 hcase33 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase321a hcase321b hcase010a hcase010b hcase001a hcase001b hcase040a hcase040b hcase131a hcase131b hcase421a hcase02 hcase03 hcase11 hcase12 hcase14 hcase31 hcase33 hcase41 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase321a hcase321b hcase010a hcase010b hcase001a hcase001b hcase041a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase321a hcase321b hcase011a hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase41 hcase42 hcase43 hcase44
              omega
      ·
        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
        ·
          rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              clear hn4 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase301a hcase301b hcase341a hcase341b hcase040b hcase000b hcase010b hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase341a hcase341b hcase040a hcase040b hcase000a hcase000b hcase011a hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase101a hcase101b hcase301a hcase301b hcase341a hcase341b hcase040a hcase040b hcase001a hcase001b hcase130b hcase01 hcase02 hcase03 hcase11 hcase12 hcase14 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase341a hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase310b hcase010a hcase010b hcase320b hcase02 hcase03 hcase11 hcase12 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase301a hcase341a hcase040b hcase001a hcase131a hcase131b hcase310b hcase010a hcase010b hcase321a hcase400b hcase420b hcase02 hcase03 hcase11 hcase12 hcase14 hcase33 hcase41 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase101b hcase301a hcase301b hcase341a hcase341b hcase040b hcase001a hcase131a hcase131b hcase310a hcase310b hcase010a hcase010b hcase321a hcase400b hcase421a hcase02 hcase03 hcase11 hcase12 hcase14 hcase33 hcase41 hcase43 hcase44
                        omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          clear hn4 hsum_nat1 hcut5 hcut36 hcut28 hcut23 hcut12 hcut26 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101a hcase101b hcase301a hcase341a hcase040b hcase001a hcase131a hcase310b hcase010b hcase321a hcase401a hcase430b hcase420b hcase02 hcase03 hcase11 hcase12 hcase14 hcase33 hcase41 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase301b hcase341a hcase341b hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase310a hcase310b hcase010a hcase010b hcase321a hcase321b hcase401a hcase430a hcase430b hcase421a hcase02 hcase03 hcase11 hcase12 hcase14 hcase33 hcase41 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase301b hcase341a hcase341b hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase310a hcase310b hcase010a hcase010b hcase321a hcase321b hcase401a hcase431a hcase02 hcase03 hcase11 hcase12 hcase14 hcase33 hcase41 hcase42 hcase44
                        omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase341a hcase341b hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase310a hcase310b hcase011a hcase02 hcase03 hcase11 hcase12 hcase14 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase301a hcase301b hcase341a hcase341b hcase040b hcase001a hcase131a hcase131b hcase410b hcase400b hcase320b hcase01 hcase02 hcase03 hcase11 hcase12 hcase14 hcase33 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase341a hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase311a hcase410a hcase410b hcase400a hcase400b hcase321a hcase01 hcase02 hcase03 hcase11 hcase12 hcase14 hcase33 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                          ·
                            clear hn4 hsum_nat3 hcut5 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101a hcase301a hcase301b hcase341a hcase341b hcase040b hcase001a hcase131a hcase410b hcase401a hcase010b hcase420b hcase430b hcase120b hcase02 hcase03 hcase11 hcase14 hcase32 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat3 hcut5 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101a hcase301a hcase301b hcase341a hcase341b hcase040b hcase001a hcase131a hcase311a hcase410b hcase401a hcase010b hcase420b hcase430b hcase121a hcase02 hcase03 hcase11 hcase14 hcase32 hcase33 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase301b hcase341a hcase341b hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase311a hcase311b hcase410a hcase410b hcase401a hcase010a hcase010b hcase420a hcase420b hcase431a hcase02 hcase03 hcase11 hcase12 hcase14 hcase32 hcase33 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase301b hcase341a hcase341b hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase311a hcase311b hcase410a hcase410b hcase401a hcase010a hcase010b hcase421a hcase02 hcase03 hcase11 hcase12 hcase14 hcase32 hcase33 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase341a hcase341b hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase311a hcase311b hcase410a hcase410b hcase401a hcase401b hcase011a hcase02 hcase03 hcase11 hcase12 hcase14 hcase32 hcase33 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase031a hcase101b hcase301a hcase301b hcase341a hcase341b hcase040b hcase001a hcase131a hcase131b hcase311a hcase311b hcase411a hcase420b hcase400b hcase01 hcase02 hcase03 hcase11 hcase12 hcase14 hcase32 hcase33 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase301b hcase341a hcase341b hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase311a hcase311b hcase411a hcase420a hcase420b hcase401a hcase01 hcase02 hcase03 hcase11 hcase12 hcase14 hcase32 hcase33 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase301a hcase301b hcase341a hcase341b hcase040a hcase040b hcase001a hcase001b hcase131a hcase131b hcase311a hcase311b hcase411a hcase421a hcase01 hcase02 hcase03 hcase11 hcase12 hcase14 hcase32 hcase33 hcase40 hcase43 hcase44
                    omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase031a hcase101a hcase101b hcase301a hcase301b hcase341a hcase341b hcase041a hcase00 hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
          omega

#print axioms symbolic_v2_mask551_integer_shard004
end Jsp404.SixExactFloorKernel
