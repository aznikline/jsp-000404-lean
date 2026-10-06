import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask223_integer_shard007 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut22 : (s02 + s10 + s11 + s42 + u02 + u10 + u11 + u42) + 1 ≤ (n))
    (hcut70 : (s03 + u03) + 1 ≤ (s13 + 2))
    (hcut24 : (s01 + s43 + u01 + u43) + 1 ≤ (s33 + 2))
    (hcut79 : (s02 + s04 + s10 + s11 + u02 + u04 + u10 + u11) + 1 ≤ (n + 1))
    (hcut30 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut65 : (s00 + s04 + s12 + s40 + s44 + u00 + u04 + u12 + u40 + u44) + 1 ≤ (2 * n))
    (hcut54 : (s00 + s43 + u00 + u43) + 1 ≤ (n + 1))
    (hcut23 : (s00 + s33 + s44 + u00 + u33 + u44) + 1 ≤ (n + 2))
    (hcut21 : (s33 + s40 + s41 + s42 + u33 + u40 + u41 + u42) + 1 ≤ (n + s01 + 2))
    (hcut63 : (s13 + s14 + s41 + u13 + u14 + u41) + 1 ≤ (n))
    (hcut61 : (s12 + s13 + s41 + u12 + u13 + u41 + 1) + 1 ≤ (n))
    (hcut75 : (s01 + s04 + s13 + s40 + s44 + u01 + u04 + u13 + u40 + u44) + 1 ≤ (2 * n))
    (hcut35 : (s02 + s11 + s31 + u02 + u11 + u31 + 1) + 1 ≤ (n))
    (hcut25 : (s03 + s11 + s42 + u03 + u11 + u42 + 1) + 1 ≤ (n))
    (hcut67 : (s00 + s12 + s40 + s41 + s44 + u00 + u12 + u40 + u41 + u44) + 1 ≤ (2 * n))
    (hcut4 : (s44 + u44) + 1 ≤ (s34 + 3))
    (hcut3 : (s02 + s03 + s14 + s40 + s41 + s42 + u02 + u03 + u14 + u40 + u41 + u42) + 1 ≤ (n + 2))
    (hcut7 : (s00 + s04 + s13 + s40 + s44 + u00 + u04 + u13 + u40 + u44) + 1 ≤ (2 * n))
    (hcut36 : (s14 + s40 + u14 + u40) + 1 ≤ (n))
    (hcut44 : (s34 + u34) + 1 ≤ (s44 + 2))
    (hcut74 : (s13 + s40 + s41 + u13 + u40 + u41) + 1 ≤ (n))
    (hcut8 : (s04 + s10 + s42 + u04 + u10 + u42) + 1 ≤ (n + 1))
    (hcut2 : (s10 + s32 + u10 + u32) + 1 ≤ (s00 + 2))
    (hcut56 : (s00 + s04 + s12 + s33 + s40 + u00 + u04 + u12 + u33 + u40) + 1 ≤ (2 * n))
    (hcut14 : (s40 + s41 + s43 + u40 + u41 + u43) + 1 ≤ (n))
    (hcut53 : (s40 + s41 + s42 + u40 + u41 + u42) + 1 ≤ (n))
    (hcut0 : (s11 + s30 + s31 + s34 + s42 + s43 + u11 + u30 + u31 + u34 + u42 + u43) + 1 ≤ (n + 1))
    (hcut27 : (s02 + s03 + s04 + s11 + s42 + u02 + u03 + u04 + u11 + u42) + 1 ≤ (n))
    (hcut43 : (s13 + s40 + u13 + u40 + 1) + 1 ≤ (n))
    (hcut45 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 1))
    (hcut77 : (s01 + s04 + s40 + s41 + s44 + u01 + u04 + u40 + u41 + u44) + 1 ≤ (2 * n + 1))
    (hcut57 : (s04 + s10 + s13 + s32 + s33 + s40 + u04 + u10 + u13 + u32 + u33 + u40) + 1 ≤ (2 * n))
    (hcut12 : (s00 + s04 + s40 + s41 + s44 + u00 + u04 + u40 + u41 + u44) + 1 ≤ (2 * n))
    (hcut62 : (s12 + s14 + s41 + u12 + u14 + u41 + 1) + 1 ≤ (n))
    (hcut51 : (s12 + s13 + s40 + u12 + u13 + u40) + 1 ≤ (n))
    (hcut1 : (s00 + s04 + s12 + s13 + s33 + s40 + s41 + s44 + u00 + u04 + u12 + u13 + u33 + u40 + u41 + u44) + 1 ≤ (2 * n + 2))
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
    (hcase120a : s12 = 0)
    (hcase120b : u12 = 0)
    (hcase100a : s10 = 0)
    (hcase100b : u10 = 0)
    : False := by
  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
  ·
    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
    ·
      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
      ·
        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            clear hsum_nat0 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase120b hcase100b hcase040a hcase040b hcase110b hcase130b hcase030a hcase030b hcase140b hcase00 hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hsum_nat0 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase120a hcase120b hcase100b hcase040a hcase040b hcase110b hcase130b hcase030a hcase030b hcase141a hcase400b hcase420b hcase440b hcase430b hcase00 hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41
                    omega
                  ·
                    clear hn4 hsum_nat0 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase120a hcase120b hcase100b hcase040a hcase040b hcase110b hcase130b hcase030a hcase030b hcase141a hcase400b hcase420b hcase440b hcase431a hcase00 hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41
                    omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                      ·
                        rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase110a hcase110b hcase130a hcase130b hcase030b hcase141a hcase141b hcase400a hcase400b hcase420a hcase420b hcase441a hcase441b hcase330a hcase330b hcase430a hcase430b hcase000b hcase010b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase130a hcase130b hcase030a hcase030b hcase141a hcase141b hcase400a hcase400b hcase420a hcase420b hcase441a hcase441b hcase330a hcase330b hcase430a hcase430b hcase000a hcase000b hcase011a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut77 hcut57 hcut12 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase120a hcase120b hcase100b hcase040a hcase040b hcase110b hcase130b hcase030a hcase030b hcase141a hcase400b hcase420b hcase441a hcase330a hcase330b hcase430b hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase130a hcase130b hcase030a hcase030b hcase141a hcase141b hcase400a hcase400b hcase420a hcase420b hcase441a hcase441b hcase330b hcase00 hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                      omega
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase110a hcase110b hcase130a hcase130b hcase030b hcase141a hcase141b hcase400a hcase400b hcase420a hcase420b hcase441a hcase441b hcase331a hcase331b hcase000b hcase010b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase130a hcase130b hcase030a hcase030b hcase141a hcase141b hcase400a hcase400b hcase420a hcase420b hcase441a hcase441b hcase331a hcase331b hcase000a hcase000b hcase011a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                        omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase120a hcase120b hcase100b hcase040a hcase040b hcase110b hcase130b hcase030a hcase030b hcase141a hcase400b hcase420b hcase441a hcase430b hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100b hcase040b hcase110a hcase110b hcase130b hcase030b hcase141a hcase400b hcase420b hcase441a hcase331a hcase001a hcase431a hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                        omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase120b hcase100b hcase040a hcase040b hcase110b hcase130b hcase030a hcase030b hcase141a hcase400a hcase400b hcase00 hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase120b hcase100b hcase040a hcase040b hcase110b hcase130b hcase030a hcase030b hcase141a hcase00 hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase130a hcase130b hcase031a hcase00 hcase01 hcase02 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
        ·
          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase430a hcase430b hcase010b hcase420a hcase420b hcase030b hcase000b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase44
                    omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hsum_nat0 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase120b hcase100b hcase040a hcase040b hcase110b hcase131a hcase140b hcase430b hcase010a hcase010b hcase420b hcase030a hcase030b hcase001a hcase001b hcase440b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120b hcase100b hcase040b hcase110b hcase131a hcase140b hcase430b hcase010b hcase420b hcase030b hcase001a hcase441a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase430a hcase430b hcase010a hcase010b hcase420a hcase420b hcase031a hcase00 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase44
                  omega
              ·
                rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase430a hcase430b hcase010b hcase000b hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase44
                  omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase120b hcase100b hcase040a hcase040b hcase110b hcase131a hcase140b hcase430b hcase010a hcase010b hcase421a hcase001a hcase001b hcase440b hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120b hcase100b hcase040a hcase040b hcase110b hcase131a hcase140b hcase430b hcase010b hcase421a hcase001a hcase441a hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41
                    omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase430a hcase430b hcase011a hcase00 hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
              omega
          ·
            rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
            ·
              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase431a hcase431b hcase000b hcase010b hcase030b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase431a hcase431b hcase000a hcase000b hcase010a hcase010b hcase031a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase431a hcase431b hcase000a hcase000b hcase011a hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
                omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase001a hcase001b hcase330b hcase01 hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase44
                omega
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat0 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase120b hcase100b hcase040a hcase040b hcase110b hcase131a hcase140b hcase431a hcase001a hcase001b hcase331a hcase331b hcase440b hcase420b hcase01 hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase431a hcase001a hcase001b hcase331a hcase331b hcase440a hcase440b hcase421a hcase01 hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41
                    omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut21 hcut63 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase120b hcase100b hcase040a hcase040b hcase110b hcase131a hcase140b hcase431a hcase331a hcase441a hcase420b hcase01 hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase431a hcase001a hcase001b hcase331a hcase331b hcase441a hcase441b hcase421a hcase01 hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41
                    omega
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase110a hcase110b hcase131a hcase131b hcase141a hcase141b hcase400a hcase400b hcase420a hcase420b hcase030b hcase430a hcase430b hcase010b hcase000b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                      omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase400b hcase420b hcase030a hcase030b hcase430b hcase010a hcase010b hcase001a hcase001b hcase440b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120b hcase100b hcase040b hcase110a hcase110b hcase131a hcase141a hcase400b hcase420b hcase030b hcase430b hcase010b hcase001a hcase441a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase141a hcase141b hcase400a hcase400b hcase420a hcase420b hcase030a hcase030b hcase430a hcase430b hcase011a hcase00 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                    omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase141a hcase141b hcase400a hcase400b hcase420a hcase420b hcase030a hcase030b hcase330b hcase00 hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase44
                    omega
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase110a hcase110b hcase131a hcase131b hcase141a hcase141b hcase400a hcase400b hcase420a hcase420b hcase030b hcase431a hcase431b hcase331a hcase331b hcase000b hcase010b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase141a hcase141b hcase400a hcase400b hcase420a hcase420b hcase030a hcase030b hcase431a hcase431b hcase331a hcase331b hcase000a hcase000b hcase011a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase44
                        omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase120b hcase100b hcase040a hcase040b hcase110b hcase131a hcase141a hcase400b hcase420b hcase030a hcase030b hcase431a hcase331a hcase331b hcase001a hcase001b hcase440b hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut21 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120b hcase100b hcase040b hcase110a hcase110b hcase131a hcase141a hcase400b hcase420b hcase030b hcase431a hcase331a hcase001a hcase441a hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                        omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase141a hcase141b hcase400a hcase400b hcase420a hcase420b hcase031a hcase00 hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43 hcase44
                omega
            ·
              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase110a hcase110b hcase131a hcase131b hcase400a hcase400b hcase010b hcase430a hcase430b hcase000b hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                    omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase400a hcase400b hcase421a hcase010a hcase010b hcase430b hcase001a hcase001b hcase440b hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase110a hcase110b hcase131a hcase131b hcase400a hcase400b hcase421a hcase010b hcase430b hcase001a hcase441a hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase141a hcase141b hcase400a hcase400b hcase421a hcase010a hcase010b hcase431a hcase00 hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase141a hcase141b hcase400a hcase400b hcase421a hcase421b hcase011a hcase00 hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43 hcase44
                omega
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                ·
                  clear hn4 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120b hcase100b hcase040b hcase110b hcase131a hcase141a hcase010b hcase430a hcase430b hcase000b hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120b hcase100b hcase040b hcase110b hcase131a hcase141a hcase010b hcase430b hcase001a hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase141a hcase141b hcase401a hcase010a hcase010b hcase431a hcase00 hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase141a hcase141b hcase401a hcase401b hcase011a hcase00 hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
    ·
      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
      ·
        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
        ·
          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase330b hcase000b hcase01 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase330a hcase330b hcase001a hcase001b hcase010a hcase010b hcase030a hcase030b hcase140b hcase130b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase330b hcase001a hcase010a hcase010b hcase030b hcase140a hcase140b hcase131a hcase131b hcase420b hcase410b hcase400b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120b hcase100b hcase040b hcase111a hcase330b hcase001a hcase010a hcase010b hcase030b hcase140b hcase131a hcase420b hcase410b hcase401a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                        omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat3 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100b hcase040b hcase111a hcase330b hcase001a hcase010a hcase010b hcase030b hcase140b hcase131a hcase420b hcase411a hcase400b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase330a hcase330b hcase001a hcase001b hcase010a hcase010b hcase030a hcase030b hcase140a hcase140b hcase131a hcase131b hcase420a hcase420b hcase411a hcase401a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                        omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut70 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase330b hcase001a hcase010a hcase010b hcase030b hcase140a hcase140b hcase131a hcase131b hcase421a hcase400b hcase410b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase330a hcase330b hcase001a hcase001b hcase010a hcase010b hcase030a hcase030b hcase140a hcase140b hcase131a hcase131b hcase421a hcase400a hcase400b hcase411a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase330a hcase330b hcase001a hcase001b hcase010a hcase010b hcase030a hcase030b hcase140a hcase140b hcase131a hcase131b hcase421a hcase401a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43 hcase44
                      omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase330a hcase330b hcase001a hcase010b hcase030b hcase141a hcase141b hcase410b hcase430b hcase400b hcase02 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase42 hcase44
                      omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                        ·
                          clear hn4 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase120b hcase100b hcase040b hcase111a hcase330a hcase330b hcase001a hcase010b hcase030a hcase030b hcase141a hcase410a hcase410b hcase430b hcase401a hcase420a hcase420b hcase130b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120b hcase100b hcase040b hcase111a hcase330a hcase330b hcase001a hcase010b hcase030b hcase141a hcase410b hcase430b hcase401a hcase420b hcase131a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase330a hcase330b hcase001a hcase001b hcase010a hcase010b hcase030a hcase030b hcase141a hcase141b hcase410a hcase410b hcase430a hcase430b hcase401a hcase421a hcase02 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase330b hcase001a hcase001b hcase010a hcase010b hcase030a hcase030b hcase141a hcase141b hcase410a hcase410b hcase02 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase40 hcase42 hcase44
                    omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat3 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut77 hcut57 hcut12 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100b hcase040b hcase111a hcase330b hcase001a hcase010a hcase010b hcase030b hcase141a hcase411a hcase130b hcase420b hcase400b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase330a hcase330b hcase001a hcase001b hcase010a hcase010b hcase030a hcase030b hcase141a hcase141b hcase411a hcase130a hcase130b hcase420a hcase420b hcase401a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase330a hcase330b hcase001a hcase001b hcase010a hcase010b hcase030a hcase030b hcase141a hcase141b hcase411a hcase130a hcase130b hcase421a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase40 hcase43 hcase44
                      omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120b hcase100b hcase040b hcase111a hcase330a hcase330b hcase001a hcase010b hcase030b hcase141a hcase411a hcase131a hcase420b hcase430b hcase400b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase330a hcase330b hcase001a hcase001b hcase010a hcase010b hcase030a hcase030b hcase141a hcase141b hcase411a hcase131a hcase131b hcase420a hcase420b hcase430a hcase430b hcase401a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase330a hcase330b hcase001a hcase001b hcase010a hcase010b hcase030a hcase030b hcase141a hcase141b hcase411a hcase131a hcase131b hcase420a hcase420b hcase431a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase40 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase330a hcase330b hcase001a hcase001b hcase010a hcase010b hcase030a hcase030b hcase141a hcase141b hcase411a hcase131a hcase131b hcase421a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase40 hcase43 hcase44
                      omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase330a hcase330b hcase001a hcase001b hcase010a hcase010b hcase031a hcase02 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase330a hcase330b hcase001a hcase001b hcase011a hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
      ·
        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase331a hcase331b hcase400a hcase400b hcase130a hcase130b hcase010b hcase030b hcase410a hcase410b hcase000b hcase02 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase331a hcase400b hcase130a hcase130b hcase010a hcase010b hcase030b hcase410b hcase001a hcase420b hcase02 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut70 hcut79 hcut30 hcut65 hcut54 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase331a hcase400b hcase130a hcase130b hcase010a hcase010b hcase030b hcase410b hcase001a hcase421a hcase02 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                      omega
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase331a hcase331b hcase400a hcase400b hcase130a hcase130b hcase010b hcase030b hcase411a hcase411b hcase000b hcase02 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase120b hcase100b hcase040a hcase040b hcase111a hcase331a hcase331b hcase400a hcase400b hcase130b hcase010a hcase010b hcase030a hcase030b hcase411a hcase411b hcase001a hcase001b hcase140b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat3 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100b hcase040b hcase111a hcase331a hcase400b hcase130b hcase010a hcase010b hcase030b hcase411a hcase001a hcase141a hcase420b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase400a hcase400b hcase130a hcase130b hcase010a hcase010b hcase030a hcase030b hcase411a hcase001a hcase001b hcase141a hcase141b hcase421a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                        omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase400a hcase400b hcase130a hcase130b hcase010a hcase010b hcase031a hcase00 hcase02 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase400a hcase400b hcase130a hcase130b hcase011a hcase00 hcase02 hcase03 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                ·
                  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase331a hcase331b hcase400a hcase400b hcase131a hcase131b hcase030b hcase410a hcase410b hcase000b hcase010b hcase02 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase400a hcase400b hcase131a hcase131b hcase030a hcase030b hcase410a hcase410b hcase000a hcase000b hcase011a hcase02 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase331a hcase400b hcase131a hcase131b hcase030b hcase410b hcase001a hcase420b hcase01 hcase02 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut70 hcut79 hcut30 hcut65 hcut54 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040b hcase331a hcase400b hcase131a hcase131b hcase030b hcase410b hcase001a hcase421a hcase01 hcase02 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                    omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                      ·
                        clear hn4 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100b hcase040b hcase111a hcase331a hcase331b hcase400a hcase400b hcase131a hcase030b hcase140b hcase010b hcase420a hcase420b hcase000b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut21 hcut63 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100b hcase040b hcase111a hcase331a hcase400b hcase131a hcase030b hcase411a hcase140b hcase010a hcase010b hcase420b hcase001a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase400a hcase400b hcase131a hcase131b hcase030a hcase030b hcase411a hcase140a hcase140b hcase010a hcase010b hcase421a hcase00 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase400a hcase400b hcase131a hcase131b hcase030a hcase030b hcase411a hcase411b hcase140a hcase140b hcase011a hcase00 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                    ·
                      clear hn4 hsum_nat3 hsum_nat4 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120b hcase100a hcase100b hcase040b hcase111a hcase331a hcase331b hcase400a hcase400b hcase131a hcase030b hcase141a hcase000b hcase010b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase400a hcase400b hcase131a hcase131b hcase030a hcase030b hcase411a hcase411b hcase141a hcase141b hcase000a hcase000b hcase011a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat3 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut21 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120b hcase100b hcase040b hcase111a hcase331a hcase400b hcase131a hcase030b hcase411a hcase141a hcase001a hcase420b hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase400a hcase400b hcase131a hcase131b hcase030a hcase030b hcase411a hcase141a hcase141b hcase001a hcase001b hcase421a hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                      omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase400a hcase400b hcase131a hcase131b hcase031a hcase00 hcase01 hcase02 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase331a hcase331b hcase401a hcase401b hcase000b hcase010b hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase401a hcase401b hcase000a hcase000b hcase011a hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase120b hcase100b hcase040a hcase040b hcase111a hcase331a hcase331b hcase401a hcase401b hcase001a hcase001b hcase140b hcase130b hcase01 hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat3 hcut22 hcut70 hcut79 hcut30 hcut65 hcut54 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120b hcase100b hcase040b hcase111a hcase331a hcase401a hcase001a hcase140b hcase131a hcase030b hcase410b hcase420b hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase401a hcase001a hcase001b hcase140a hcase140b hcase131a hcase131b hcase030a hcase030b hcase410a hcase410b hcase421a hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase401a hcase001a hcase001b hcase140a hcase140b hcase131a hcase131b hcase030a hcase030b hcase411a hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase401a hcase401b hcase001a hcase001b hcase140a hcase140b hcase131a hcase131b hcase031a hcase01 hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          clear hn4 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase120b hcase100b hcase040b hcase111a hcase401a hcase001a hcase141a hcase030a hcase030b hcase410a hcase410b hcase420a hcase420b hcase130b hcase010b hcase430b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase401a hcase001a hcase001b hcase141a hcase141b hcase030a hcase030b hcase410a hcase410b hcase420a hcase420b hcase130a hcase130b hcase010a hcase010b hcase431a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase401a hcase401b hcase001a hcase001b hcase141a hcase141b hcase030a hcase030b hcase410a hcase410b hcase420a hcase420b hcase130a hcase130b hcase011a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                        omega
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          clear hn4 hsum_nat3 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut21 hcut63 hcut61 hcut75 hcut25 hcut67 hcut4 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase021a hcase120b hcase100b hcase040b hcase111a hcase401a hcase001a hcase141a hcase030b hcase410b hcase420b hcase131a hcase010b hcase430b hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase401a hcase001a hcase001b hcase141a hcase141b hcase030a hcase030b hcase410a hcase410b hcase420a hcase420b hcase131a hcase131b hcase010a hcase010b hcase431a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase401a hcase401b hcase001a hcase001b hcase141a hcase141b hcase030a hcase030b hcase410a hcase410b hcase420a hcase420b hcase131a hcase131b hcase011a hcase02 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase401a hcase001a hcase001b hcase141a hcase141b hcase030a hcase030b hcase410a hcase410b hcase421a hcase01 hcase02 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase021a hcase021b hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase401a hcase001a hcase001b hcase141a hcase141b hcase030a hcase030b hcase411a hcase01 hcase02 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase040a hcase040b hcase111a hcase111b hcase331a hcase331b hcase401a hcase401b hcase001a hcase001b hcase141a hcase141b hcase031a hcase01 hcase02 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
  ·
    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut22 hcut70 hcut24 hcut79 hcut30 hcut65 hcut54 hcut23 hcut21 hcut63 hcut61 hcut75 hcut35 hcut25 hcut67 hcut4 hcut3 hcut7 hcut36 hcut44 hcut74 hcut8 hcut2 hcut56 hcut14 hcut53 hcut0 hcut27 hcut43 hcut45 hcut77 hcut57 hcut12 hcut62 hcut51 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase021a hcase120a hcase120b hcase100a hcase100b hcase041a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
    omega

#print axioms symbolic_v2_mask223_integer_shard007
end Jsp404.SixExactFloorKernel
