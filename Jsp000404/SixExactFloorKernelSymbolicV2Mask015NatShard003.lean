import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask15_integer_shard003 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut55 : (s10 + s11 + s32 + s44 + u10 + u11 + u32 + u44) + 1 ≤ (n + 1))
    (hcut70 : (s14 + s32 + s33 + s34 + s40 + u14 + u32 + u33 + u34 + u40 + 1) + 1 ≤ (2 * n))
    (hcut14 : (s10 + s11 + s12 + u10 + u11 + u12 + 1) + 1 ≤ (n))
    (hcut72 : (s00 + s04 + s13 + s40 + s44 + u00 + u04 + u13 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut53 : (s31 + s32 + s44 + u31 + u32 + u44) + 1 ≤ (n))
    (hcut17 : (s12 + s14 + s30 + u12 + u14 + u30) + 1 ≤ (n))
    (hcut22 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut73 : (s02 + s03 + s14 + u02 + u03 + u14 + 2) + 1 ≤ (n))
    (hcut42 : (s01 + s02 + s03 + u01 + u02 + u03 + 2) + 1 ≤ (n))
    (hcut60 : (s02 + s03 + s32 + u02 + u03 + u32 + 2) + 1 ≤ (n))
    (hcut7 : (s12 + s13 + s30 + u12 + u13 + u30) + 1 ≤ (n))
    (hcut33 : (s02 + s10 + s14 + u02 + u10 + u14 + 1) + 1 ≤ (n))
    (hcut64 : (s01 + s02 + s42 + s43 + u01 + u02 + u42 + u43) + 1 ≤ (s33 + 2))
    (hcut11 : (s10 + s32 + s40 + u10 + u32 + u40 + 3) + 1 ≤ (2 * n))
    (hcut59 : (s02 + s10 + s11 + s14 + u02 + u10 + u11 + u14) + 1 ≤ (n))
    (hcut57 : (s10 + s11 + s13 + s40 + s43 + u10 + u11 + u13 + u40 + u43 + 2) + 1 ≤ (2 * n))
    (hcut37 : (s40 + s41 + s42 + u40 + u41 + u42) + 1 ≤ (n))
    (hcut66 : (s02 + s03 + s10 + s11 + s31 + u02 + u03 + u10 + u11 + u31 + 1) + 1 ≤ (n))
    (hcut23 : (s01 + u01) + 1 ≤ (s33 + 1))
    (hcut71 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 1))
    (hcut32 : (s43 + u43) + 1 ≤ (s33 + 1))
    (hcut51 : (s10 + s11 + s14 + s31 + u10 + u11 + u14 + u31) + 1 ≤ (n))
    (hcut5 : (s13 + s14 + s40 + u13 + u14 + u40) + 1 ≤ (n + 2))
    (hcut34 : (s00 + s33 + u00 + u33) + 1 ≤ (n + 1))
    (hcut2 : (s03 + s41 + u03 + u41) + 1 ≤ (s13 + 2))
    (hcut9 : (s11 + s40 + u11 + u40 + 4) + 1 ≤ (2 * n))
    (hcut50 : (s11 + s14 + s31 + u11 + u14 + u31 + 1) + 1 ≤ (n))
    (hcut3 : (s34 + u34) + 1 ≤ (s44 + 2))
    (hcut43 : (s31 + s32 + s40 + u31 + u32 + u40 + 3) + 1 ≤ (2 * n))
    (hcut1 : (s00 + s04 + s13 + s33 + s40 + s44 + u00 + u04 + u13 + u33 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut28 : (s31 + s32 + s33 + s40 + u31 + u32 + u33 + u40) + 1 ≤ (n + s12 + 2))
    (hcut29 : (s00 + s33 + s44 + u00 + u33 + u44) + 1 ≤ (n + 2))
    (hcut0 : (s02 + s30 + s31 + s32 + s34 + s42 + s43 + u02 + u30 + u31 + u32 + u34 + u42 + u43) + 1 ≤ (n + 1))
    (hcut26 : (s01 + s02 + s14 + s31 + u01 + u02 + u14 + u31) + 1 ≤ (n))
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
    (hcase001a : 1 ≤ s00)
    (hcase001b : u00 = 1)
    (hcase131a : 1 ≤ s13)
    (hcase131b : u13 = 1)
    (hcase040a : s04 = 0)
    (hcase040b : u04 = 0)
    (hcase301a : 1 ≤ s30)
    (hcase301b : u30 = 1)
    : False := by
  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
  ·
    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
    ·
      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
      ·
        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase040b hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140a hcase140b hcase120a hcase120b hcase310a hcase310b hcase400b hcase410b hcase00 hcase04 hcase10 hcase11 hcase13 hcase30 hcase32 hcase34 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase030a hcase030b hcase020b hcase010b hcase330b hcase140a hcase140b hcase120a hcase120b hcase310a hcase310b hcase400b hcase411a hcase420b hcase00 hcase04 hcase10 hcase11 hcase13 hcase30 hcase32 hcase34 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase120a hcase120b hcase310a hcase310b hcase400a hcase400b hcase411a hcase421a hcase00 hcase04 hcase10 hcase11 hcase13 hcase30 hcase32 hcase34 hcase43 hcase44
                      omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase040a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140a hcase140b hcase120a hcase120b hcase310b hcase401a hcase401b hcase440a hcase440b hcase340b hcase320b hcase00 hcase04 hcase10 hcase11 hcase13 hcase30 hcase41 hcase42 hcase43
                        omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                            ·
                              clear hn4 hsum_nat0 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140b hcase120a hcase120b hcase310b hcase401a hcase440b hcase340b hcase321a hcase410b hcase420b hcase110b hcase00 hcase04 hcase10 hcase13 hcase30 hcase43
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140b hcase120b hcase310a hcase310b hcase401a hcase440b hcase340a hcase340b hcase321a hcase321b hcase410b hcase420b hcase111a hcase00 hcase04 hcase10 hcase13 hcase30 hcase43
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase120a hcase120b hcase310a hcase310b hcase401a hcase440a hcase440b hcase340a hcase340b hcase321a hcase321b hcase410a hcase410b hcase421a hcase00 hcase04 hcase10 hcase11 hcase13 hcase30 hcase43
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase120a hcase120b hcase310a hcase310b hcase401a hcase440a hcase440b hcase340a hcase340b hcase321a hcase321b hcase411a hcase00 hcase04 hcase10 hcase11 hcase13 hcase30 hcase42 hcase43
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase120a hcase120b hcase310a hcase310b hcase401a hcase401b hcase440b hcase00 hcase04 hcase10 hcase11 hcase13 hcase30 hcase32 hcase41 hcase42 hcase43
                      omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase020b hcase010b hcase330a hcase330b hcase140a hcase140b hcase120a hcase120b hcase310a hcase310b hcase401a hcase401b hcase00 hcase04 hcase10 hcase11 hcase13 hcase30 hcase32 hcase34 hcase41 hcase42 hcase43
                    omega
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140b hcase120a hcase120b hcase311a hcase311b hcase100b hcase110b hcase00 hcase04 hcase13 hcase30 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140b hcase120a hcase120b hcase311a hcase100a hcase100b hcase111a hcase340b hcase440a hcase440b hcase410a hcase410b hcase320b hcase00 hcase04 hcase13 hcase30 hcase40 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase120b hcase100a hcase100b hcase111a hcase111b hcase340a hcase340b hcase440b hcase410b hcase00 hcase04 hcase13 hcase30 hcase40 hcase42 hcase43
                            omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140a hcase140b hcase120a hcase120b hcase311a hcase311b hcase100a hcase100b hcase111a hcase111b hcase340a hcase340b hcase440b hcase411a hcase400b hcase00 hcase04 hcase13 hcase30 hcase32 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase120a hcase120b hcase311a hcase311b hcase100a hcase100b hcase111a hcase111b hcase340a hcase340b hcase440a hcase440b hcase411a hcase401a hcase00 hcase04 hcase13 hcase30 hcase32 hcase42 hcase43
                            omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase020b hcase010b hcase330a hcase330b hcase140a hcase140b hcase120a hcase120b hcase311a hcase311b hcase100a hcase100b hcase111a hcase111b hcase340a hcase340b hcase00 hcase04 hcase13 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43
                        omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase120a hcase120b hcase311a hcase311b hcase100a hcase100b hcase111a hcase111b hcase440b hcase00 hcase04 hcase13 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase020b hcase010b hcase330a hcase330b hcase140a hcase140b hcase120a hcase120b hcase311a hcase311b hcase100a hcase100b hcase111a hcase111b hcase341a hcase341b hcase00 hcase04 hcase13 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43
                        omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140b hcase120a hcase120b hcase311a hcase101a hcase320b hcase440a hcase440b hcase340b hcase00 hcase04 hcase11 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase120a hcase120b hcase311a hcase311b hcase101a hcase101b hcase320a hcase320b hcase440b hcase00 hcase04 hcase11 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43
                        omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase020b hcase010b hcase330a hcase330b hcase140a hcase140b hcase120a hcase120b hcase311a hcase311b hcase101a hcase101b hcase320a hcase320b hcase00 hcase04 hcase11 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43
                      omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase120b hcase101a hcase101b hcase440b hcase410b hcase00 hcase04 hcase11 hcase13 hcase30 hcase34 hcase40 hcase42 hcase43
                        omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140a hcase140b hcase120a hcase120b hcase311a hcase101a hcase101b hcase321a hcase440b hcase411a hcase400b hcase00 hcase04 hcase11 hcase13 hcase30 hcase34 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase120a hcase120b hcase311a hcase311b hcase101a hcase101b hcase321a hcase321b hcase440a hcase440b hcase411a hcase401a hcase00 hcase04 hcase11 hcase13 hcase30 hcase34 hcase42 hcase43
                          omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase020b hcase010b hcase330a hcase330b hcase140a hcase140b hcase120a hcase120b hcase311a hcase311b hcase101a hcase101b hcase321a hcase321b hcase00 hcase04 hcase11 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43
                      omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140b hcase121a hcase110b hcase310a hcase310b hcase100b hcase00 hcase04 hcase13 hcase30 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase040b hcase301a hcase030b hcase020b hcase010b hcase330b hcase140a hcase140b hcase110a hcase110b hcase310b hcase101a hcase101b hcase320b hcase00 hcase04 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          clear hn4 hsum_nat0 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140b hcase121a hcase110b hcase310b hcase101a hcase321a hcase340b hcase410b hcase00 hcase04 hcase13 hcase30 hcase40 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat0 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140b hcase110a hcase110b hcase310b hcase101a hcase321a hcase340b hcase411a hcase400b hcase00 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase121a hcase121b hcase110a hcase110b hcase310a hcase310b hcase101a hcase101b hcase321a hcase321b hcase340a hcase340b hcase411a hcase401a hcase00 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                            omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase121a hcase121b hcase110a hcase110b hcase310a hcase310b hcase101a hcase101b hcase321a hcase321b hcase440b hcase00 hcase04 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140b hcase121a hcase110a hcase110b hcase310b hcase101a hcase321a hcase341a hcase441a hcase00 hcase04 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43
                          omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140b hcase121a hcase110a hcase110b hcase311a hcase320b hcase340b hcase00 hcase04 hcase10 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140b hcase121a hcase110b hcase311a hcase311b hcase320a hcase320b hcase341a hcase341b hcase100b hcase00 hcase04 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010b hcase330b hcase140b hcase121a hcase110a hcase110b hcase311a hcase320b hcase341a hcase101a hcase00 hcase04 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140a hcase140b hcase110a hcase110b hcase311a hcase321a hcase340b hcase400b hcase00 hcase04 hcase10 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase040b hcase301a hcase030b hcase020a hcase020b hcase010b hcase330b hcase140a hcase140b hcase121a hcase110a hcase110b hcase311a hcase321a hcase340b hcase401a hcase410b hcase00 hcase04 hcase10 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase121a hcase121b hcase110a hcase110b hcase311a hcase311b hcase321a hcase321b hcase340a hcase340b hcase401a hcase411a hcase00 hcase04 hcase10 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase121a hcase121b hcase110a hcase110b hcase311a hcase321a hcase341a hcase00 hcase04 hcase10 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140b hcase121a hcase111a hcase340b hcase320b hcase00 hcase04 hcase10 hcase13 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat0 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140b hcase111a hcase340b hcase321a hcase310b hcase400b hcase00 hcase04 hcase10 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat0 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase040a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140b hcase121a hcase111a hcase340b hcase321a hcase310b hcase401a hcase410b hcase420b hcase00 hcase04 hcase10 hcase13 hcase30 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase121a hcase121b hcase111a hcase111b hcase340a hcase340b hcase321a hcase321b hcase310a hcase310b hcase401a hcase410a hcase410b hcase421a hcase00 hcase04 hcase10 hcase13 hcase30 hcase43 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase121a hcase121b hcase111a hcase111b hcase340a hcase340b hcase321a hcase321b hcase310a hcase310b hcase401a hcase411a hcase00 hcase04 hcase10 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase040a hcase040b hcase301a hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140a hcase140b hcase121a hcase111a hcase111b hcase340b hcase321a hcase311a hcase440b hcase410b hcase00 hcase04 hcase10 hcase13 hcase30 hcase40 hcase42 hcase43
                          omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase140a hcase140b hcase111a hcase111b hcase340a hcase340b hcase321a hcase311a hcase440b hcase411a hcase400b hcase00 hcase04 hcase10 hcase13 hcase30 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase121a hcase121b hcase111a hcase111b hcase340a hcase340b hcase321a hcase321b hcase311a hcase311b hcase440a hcase440b hcase411a hcase401a hcase00 hcase04 hcase10 hcase13 hcase30 hcase42 hcase43
                            omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase020b hcase010b hcase330a hcase330b hcase140a hcase140b hcase121a hcase121b hcase111a hcase111b hcase340a hcase340b hcase321a hcase321b hcase311a hcase311b hcase00 hcase04 hcase10 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43
                        omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase140a hcase140b hcase121a hcase121b hcase111a hcase111b hcase440b hcase00 hcase04 hcase10 hcase13 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase020b hcase010b hcase330a hcase330b hcase140a hcase140b hcase121a hcase121b hcase111a hcase111b hcase341a hcase341b hcase00 hcase04 hcase10 hcase13 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43
                    omega
          ·
            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase141a hcase141b hcase440b hcase410b hcase400b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase440b hcase410b hcase401a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43
                  omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330b hcase141b hcase440b hcase411a hcase400b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase330a hcase330b hcase141a hcase141b hcase440a hcase440b hcase411a hcase401a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43
                  omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase020b hcase010b hcase330a hcase330b hcase141a hcase141b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43
              omega
        ·
          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase020b hcase010b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase020a hcase020b hcase330b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase020b hcase011a hcase331a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
    ·
      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase330b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
      ·
        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase030a hcase030b hcase021a hcase021b hcase331a hcase331b hcase340a hcase340b hcase320a hcase320b hcase010a hcase010b hcase140b hcase100b hcase110b hcase00 hcase04 hcase12 hcase13 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase030a hcase030b hcase021a hcase331a hcase340b hcase320b hcase010b hcase140b hcase100a hcase100b hcase111a hcase00 hcase04 hcase12 hcase13 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase030a hcase030b hcase021a hcase331a hcase340b hcase320b hcase010b hcase140b hcase101a hcase00 hcase04 hcase11 hcase12 hcase13 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase030a hcase030b hcase021a hcase331a hcase340b hcase320b hcase010b hcase141a hcase110b hcase100b hcase310b hcase00 hcase04 hcase12 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase030b hcase021a hcase331a hcase340b hcase320b hcase010a hcase010b hcase141a hcase110b hcase100b hcase311a hcase00 hcase04 hcase12 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase030b hcase021a hcase331a hcase340b hcase320b hcase010b hcase141a hcase110b hcase101a hcase310b hcase00 hcase04 hcase12 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase030a hcase030b hcase021a hcase331a hcase340b hcase320b hcase010b hcase141a hcase141b hcase110a hcase110b hcase311a hcase400b hcase00 hcase04 hcase12 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut22 hcut73 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase030b hcase021a hcase331a hcase340b hcase320b hcase010b hcase141a hcase110a hcase110b hcase101a hcase311a hcase401a hcase410b hcase00 hcase04 hcase12 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase021b hcase331a hcase331b hcase340a hcase340b hcase320a hcase320b hcase010a hcase010b hcase141a hcase141b hcase110a hcase110b hcase101a hcase101b hcase311a hcase311b hcase401a hcase411a hcase00 hcase04 hcase12 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                ·
                  rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase331a hcase340a hcase340b hcase320a hcase320b hcase010a hcase010b hcase141b hcase111b hcase120a hcase120b hcase400b hcase00 hcase04 hcase10 hcase13 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase030b hcase021a hcase331a hcase340b hcase320b hcase010b hcase141a hcase111a hcase120a hcase120b hcase401a hcase401b hcase310b hcase00 hcase04 hcase10 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut2 hcut9 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase030b hcase021a hcase331a hcase340b hcase320b hcase010b hcase141a hcase111a hcase120b hcase401a hcase100b hcase410b hcase00 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase021b hcase331a hcase331b hcase340a hcase340b hcase320a hcase320b hcase010a hcase010b hcase141a hcase141b hcase111a hcase111b hcase120a hcase120b hcase401a hcase311a hcase311b hcase100a hcase100b hcase411a hcase00 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase021b hcase331a hcase331b hcase340a hcase340b hcase320a hcase320b hcase010a hcase010b hcase141a hcase111a hcase120a hcase120b hcase401a hcase401b hcase311a hcase311b hcase101a hcase00 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                          omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase021b hcase331a hcase331b hcase340a hcase340b hcase320a hcase320b hcase010a hcase010b hcase141a hcase111a hcase121a hcase00 hcase04 hcase10 hcase13 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase331a hcase331b hcase340a hcase340b hcase320a hcase320b hcase011a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase030a hcase030b hcase021a hcase331a hcase340b hcase321a hcase010b hcase310b hcase100b hcase140b hcase110b hcase00 hcase04 hcase12 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase030a hcase030b hcase021a hcase331a hcase340b hcase321a hcase010b hcase310b hcase100a hcase100b hcase140a hcase140b hcase111a hcase111b hcase120a hcase120b hcase400b hcase00 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase331a hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase100a hcase100b hcase140b hcase111a hcase120b hcase401a hcase410b hcase00 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase021b hcase331a hcase331b hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase100a hcase100b hcase140a hcase140b hcase111a hcase111b hcase120a hcase120b hcase401a hcase411a hcase00 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                            omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase040b hcase301a hcase030b hcase021a hcase331a hcase340b hcase321a hcase010a hcase010b hcase310a hcase310b hcase100a hcase100b hcase140a hcase140b hcase111a hcase111b hcase121a hcase440b hcase410b hcase00 hcase04 hcase13 hcase30 hcase40 hcase42 hcase43
                            omega
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase030a hcase030b hcase021a hcase331a hcase340b hcase321a hcase010b hcase310b hcase100a hcase100b hcase140a hcase140b hcase111a hcase111b hcase440b hcase411a hcase400b hcase00 hcase04 hcase13 hcase30 hcase42 hcase43
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase021b hcase331a hcase331b hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase100a hcase100b hcase140a hcase140b hcase111a hcase111b hcase121a hcase121b hcase440a hcase440b hcase411a hcase401a hcase00 hcase04 hcase13 hcase30 hcase42 hcase43
                              omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase021a hcase331a hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase100a hcase100b hcase140a hcase140b hcase111a hcase111b hcase121a hcase121b hcase00 hcase04 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43
                          omega
                  ·
                    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase030a hcase030b hcase021a hcase331a hcase340b hcase321a hcase010b hcase310b hcase100a hcase100b hcase141a hcase141b hcase120a hcase120b hcase110a hcase110b hcase400b hcase00 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase301b hcase030a hcase030b hcase331a hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase100b hcase120b hcase110b hcase401a hcase410b hcase00 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase021b hcase331a hcase331b hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase100a hcase100b hcase141a hcase141b hcase120a hcase120b hcase110a hcase110b hcase401a hcase411a hcase00 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                            omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase040b hcase301a hcase301b hcase030b hcase021a hcase331a hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase440b hcase410b hcase00 hcase04 hcase13 hcase30 hcase40 hcase42 hcase43
                            omega
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase331a hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase100a hcase100b hcase141b hcase120a hcase120b hcase111b hcase440b hcase411a hcase400b hcase00 hcase04 hcase13 hcase30 hcase42 hcase43
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase021b hcase331a hcase331b hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase100a hcase100b hcase141a hcase141b hcase120a hcase120b hcase111a hcase111b hcase440a hcase440b hcase411a hcase401a hcase00 hcase04 hcase13 hcase30 hcase42 hcase43
                              omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase021a hcase331a hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase100a hcase100b hcase141a hcase141b hcase120a hcase120b hcase111a hcase111b hcase00 hcase04 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43
                          omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase331a hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase100a hcase100b hcase141b hcase121b hcase400b hcase00 hcase04 hcase11 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase040b hcase301a hcase301b hcase030b hcase021a hcase331a hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase100a hcase100b hcase121a hcase121b hcase401a hcase410b hcase00 hcase04 hcase11 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase021b hcase331a hcase331b hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase100a hcase100b hcase141a hcase141b hcase121a hcase121b hcase401a hcase411a hcase00 hcase04 hcase11 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301b hcase030b hcase021a hcase331a hcase331b hcase340a hcase340b hcase321b hcase010a hcase010b hcase310a hcase310b hcase101a hcase101b hcase110a hcase110b hcase410b hcase400b hcase00 hcase04 hcase12 hcase13 hcase14 hcase30 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                        ·
                          clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040a hcase040b hcase301a hcase301b hcase030b hcase331a hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase101a hcase110b hcase410b hcase401a hcase120b hcase00 hcase04 hcase13 hcase14 hcase30 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase040b hcase301a hcase030b hcase021a hcase331a hcase340b hcase321a hcase010a hcase010b hcase310a hcase310b hcase101a hcase101b hcase110a hcase110b hcase410b hcase401a hcase121a hcase00 hcase04 hcase13 hcase14 hcase30 hcase42 hcase43 hcase44
                          omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase331a hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase101b hcase110a hcase110b hcase411a hcase440b hcase400b hcase00 hcase04 hcase12 hcase13 hcase14 hcase30 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase021b hcase331a hcase331b hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase101a hcase101b hcase110a hcase110b hcase411a hcase440a hcase440b hcase401a hcase00 hcase04 hcase12 hcase13 hcase14 hcase30 hcase42 hcase43
                          omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase021a hcase331a hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase101a hcase101b hcase110a hcase110b hcase411a hcase411b hcase00 hcase04 hcase12 hcase13 hcase14 hcase30 hcase40 hcase42 hcase43
                        omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                        ·
                          clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase301b hcase030b hcase331a hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase101a hcase111a hcase440b hcase410b hcase120b hcase00 hcase04 hcase13 hcase14 hcase30 hcase40 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase021b hcase331a hcase331b hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase101a hcase111a hcase440a hcase440b hcase410a hcase410b hcase121a hcase00 hcase04 hcase13 hcase14 hcase30 hcase40 hcase42 hcase43
                          omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase331a hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase101b hcase111b hcase440b hcase411a hcase400b hcase00 hcase04 hcase12 hcase13 hcase14 hcase30 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase021b hcase331a hcase331b hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase101a hcase101b hcase111a hcase111b hcase440a hcase440b hcase411a hcase401a hcase00 hcase04 hcase12 hcase13 hcase14 hcase30 hcase42 hcase43
                          omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase021a hcase331a hcase340a hcase340b hcase321a hcase321b hcase010a hcase010b hcase310a hcase310b hcase101a hcase101b hcase111a hcase111b hcase00 hcase04 hcase12 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43
                      omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase030a hcase030b hcase021a hcase021b hcase331a hcase340a hcase340b hcase321a hcase010a hcase010b hcase311a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase331a hcase331b hcase340a hcase340b hcase321a hcase321b hcase011a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase030a hcase030b hcase021a hcase021b hcase331a hcase331b hcase440b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43
            omega
          ·
            clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase030b hcase021a hcase331a hcase341a hcase341b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43
            omega
  ·
    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
    ·
      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
      ·
        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase310b hcase120a hcase120b hcase110a hcase110b hcase330b hcase020a hcase020b hcase320b hcase340b hcase00 hcase04 hcase10 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110b hcase330a hcase330b hcase020a hcase020b hcase320a hcase320b hcase341a hcase341b hcase400a hcase400b hcase140b hcase410a hcase410b hcase100b hcase00 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase031a hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase330b hcase020a hcase020b hcase320a hcase320b hcase341a hcase341b hcase400b hcase140a hcase140b hcase410b hcase00 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase031a hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase330b hcase020a hcase020b hcase320a hcase320b hcase341a hcase341b hcase400b hcase140a hcase140b hcase411a hcase00 hcase04 hcase10 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310b hcase120a hcase120b hcase110a hcase110b hcase330b hcase020a hcase020b hcase320b hcase341a hcase400b hcase00 hcase04 hcase10 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase330a hcase330b hcase020a hcase020b hcase320a hcase320b hcase401a hcase401b hcase410a hcase410b hcase420a hcase420b hcase440b hcase00 hcase04 hcase10 hcase13 hcase14 hcase30 hcase43
                            omega
                          ·
                            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                            ·
                              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                              ·
                                clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut53 hcut17 hcut22 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase010b hcase310a hcase310b hcase120b hcase110b hcase330b hcase020a hcase020b hcase320a hcase320b hcase341a hcase341b hcase401a hcase410b hcase420b hcase441a hcase140a hcase140b hcase100b hcase00 hcase04 hcase13 hcase30 hcase43
                                omega
                              ·
                                clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase010b hcase310a hcase310b hcase120b hcase110a hcase110b hcase330b hcase020a hcase020b hcase320a hcase320b hcase341a hcase341b hcase401a hcase410b hcase420b hcase441a hcase140b hcase101a hcase00 hcase04 hcase13 hcase30 hcase43
                                omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut51 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase301b hcase031a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase330b hcase020b hcase320a hcase320b hcase341a hcase341b hcase401a hcase410a hcase410b hcase420b hcase441a hcase00 hcase04 hcase10 hcase13 hcase30 hcase43
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase330a hcase330b hcase020a hcase020b hcase320a hcase320b hcase341a hcase341b hcase401a hcase410a hcase410b hcase421a hcase00 hcase04 hcase10 hcase13 hcase14 hcase30 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase330a hcase330b hcase020a hcase020b hcase320a hcase320b hcase341a hcase341b hcase401a hcase411a hcase00 hcase04 hcase10 hcase13 hcase14 hcase30 hcase42 hcase43 hcase44
                        omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase010a hcase010b hcase310b hcase120a hcase120b hcase110a hcase110b hcase330b hcase020a hcase020b hcase321a hcase400b hcase340b hcase00 hcase04 hcase10 hcase13 hcase14 hcase30 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase031a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase330b hcase020a hcase020b hcase321a hcase400b hcase341a hcase00 hcase04 hcase10 hcase13 hcase14 hcase30 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase010a hcase010b hcase310b hcase120a hcase120b hcase110b hcase330b hcase020a hcase020b hcase321a hcase401a hcase401b hcase410a hcase410b hcase140b hcase340b hcase100b hcase00 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                            omega
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              clear hn4 hsum_nat0 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase310b hcase120a hcase120b hcase110b hcase330b hcase020a hcase020b hcase321a hcase401a hcase410b hcase140b hcase340b hcase101a hcase420b hcase00 hcase04 hcase13 hcase30 hcase43 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase330a hcase330b hcase020a hcase020b hcase321a hcase321b hcase401a hcase410a hcase410b hcase140a hcase140b hcase340a hcase340b hcase101a hcase101b hcase421a hcase00 hcase04 hcase13 hcase30 hcase43 hcase44
                              omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120b hcase110b hcase330b hcase020a hcase020b hcase401a hcase410b hcase140a hcase140b hcase341a hcase440b hcase00 hcase04 hcase10 hcase13 hcase30 hcase42 hcase43
                            omega
                          ·
                            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                            ·
                              clear hn4 hcut55 hcut70 hcut14 hcut53 hcut17 hcut22 hcut73 hcut42 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040a hcase040b hcase301a hcase031a hcase010b hcase310a hcase310b hcase120b hcase110b hcase330b hcase020a hcase020b hcase401a hcase410b hcase140b hcase341a hcase441a hcase100b hcase00 hcase04 hcase13 hcase30 hcase42 hcase43
                              omega
                            ·
                              clear hn4 hcut55 hcut70 hcut14 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040a hcase040b hcase301a hcase031a hcase010b hcase310a hcase310b hcase120b hcase110a hcase110b hcase330b hcase020a hcase020b hcase321a hcase401a hcase410b hcase140b hcase341a hcase441a hcase101a hcase00 hcase04 hcase13 hcase30 hcase42 hcase43
                              omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase330b hcase020a hcase020b hcase321a hcase401a hcase410b hcase440b hcase00 hcase04 hcase10 hcase13 hcase30 hcase34 hcase42 hcase43
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut51 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase301b hcase031a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase330b hcase020b hcase321a hcase321b hcase401a hcase410a hcase410b hcase441a hcase420b hcase00 hcase04 hcase10 hcase13 hcase30 hcase34 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase330a hcase330b hcase020a hcase020b hcase321a hcase321b hcase401a hcase410a hcase410b hcase141a hcase141b hcase441a hcase441b hcase421a hcase00 hcase04 hcase10 hcase13 hcase30 hcase34 hcase43
                            omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase330a hcase330b hcase020a hcase020b hcase321a hcase321b hcase401a hcase411a hcase00 hcase04 hcase10 hcase13 hcase14 hcase30 hcase34 hcase42 hcase43 hcase44
                      omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase330a hcase330b hcase021a hcase00 hcase04 hcase10 hcase13 hcase14 hcase30 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110b hcase331a hcase331b hcase340a hcase340b hcase400a hcase400b hcase140b hcase320a hcase320b hcase100b hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase340b hcase400a hcase400b hcase140b hcase320b hcase101a hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase340b hcase400b hcase140a hcase140b hcase321a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase340b hcase400b hcase320b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase340b hcase400b hcase141a hcase141b hcase321a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310b hcase120a hcase120b hcase110b hcase331a hcase340b hcase401a hcase401b hcase320b hcase100b hcase00 hcase02 hcase04 hcase13 hcase14 hcase30 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase340b hcase401a hcase401b hcase320b hcase101a hcase140b hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase340b hcase401a hcase320b hcase101a hcase141a hcase420b hcase430b hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase331b hcase340a hcase340b hcase401a hcase320a hcase320b hcase101a hcase101b hcase141a hcase141b hcase420a hcase420b hcase431a hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase331b hcase340a hcase340b hcase401a hcase320a hcase320b hcase101a hcase101b hcase141a hcase141b hcase421a hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase43 hcase44
                          omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110b hcase331a hcase331b hcase340a hcase340b hcase401a hcase401b hcase321a hcase321b hcase410a hcase410b hcase100b hcase140b hcase00 hcase02 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase301b hcase031a hcase010a hcase010b hcase310a hcase310b hcase120b hcase110b hcase331a hcase340a hcase340b hcase401a hcase410b hcase100b hcase141a hcase00 hcase02 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                            ·
                              clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase010b hcase310a hcase310b hcase120b hcase110a hcase110b hcase340a hcase340b hcase401a hcase321a hcase321b hcase410b hcase101a hcase420b hcase430b hcase140b hcase00 hcase02 hcase04 hcase13 hcase30 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase301b hcase031a hcase010b hcase310a hcase310b hcase120b hcase110a hcase110b hcase340a hcase340b hcase401a hcase321a hcase321b hcase410b hcase101a hcase420b hcase430b hcase141a hcase00 hcase02 hcase04 hcase13 hcase30 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase331b hcase340a hcase340b hcase401a hcase321a hcase321b hcase410a hcase410b hcase101a hcase101b hcase420a hcase420b hcase431a hcase00 hcase02 hcase04 hcase13 hcase14 hcase30 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase331b hcase340a hcase340b hcase401a hcase321a hcase321b hcase410a hcase410b hcase101a hcase101b hcase421a hcase00 hcase02 hcase04 hcase13 hcase14 hcase30 hcase43 hcase44
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase331b hcase340a hcase340b hcase401a hcase321a hcase321b hcase411a hcase00 hcase02 hcase04 hcase10 hcase13 hcase14 hcase30 hcase42 hcase43 hcase44
                      omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110b hcase331a hcase331b hcase341a hcase341b hcase400a hcase400b hcase140b hcase100b hcase00 hcase02 hcase04 hcase13 hcase30 hcase32 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase031a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase341a hcase400b hcase140a hcase140b hcase410b hcase00 hcase02 hcase04 hcase13 hcase30 hcase32 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase031a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase341a hcase400b hcase140a hcase140b hcase101b hcase411a hcase00 hcase02 hcase04 hcase13 hcase30 hcase32 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut43 hcut1 hcut28 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase341a hcase400b hcase320b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase341a hcase400a hcase400b hcase141a hcase141b hcase321a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                            ·
                              clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase010b hcase310a hcase310b hcase120b hcase110b hcase341a hcase341b hcase401a hcase020a hcase020b hcase140a hcase140b hcase410b hcase420b hcase430b hcase100b hcase00 hcase04 hcase13 hcase30 hcase32 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase010b hcase310a hcase310b hcase120b hcase110a hcase110b hcase341a hcase341b hcase401a hcase020a hcase020b hcase140b hcase410b hcase420b hcase430b hcase101a hcase00 hcase04 hcase13 hcase30 hcase32 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase331b hcase341a hcase341b hcase401a hcase020a hcase020b hcase140a hcase140b hcase410a hcase410b hcase420a hcase420b hcase431a hcase00 hcase04 hcase10 hcase13 hcase30 hcase32 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase331b hcase341a hcase341b hcase401a hcase020a hcase020b hcase140a hcase140b hcase410a hcase410b hcase421a hcase00 hcase04 hcase10 hcase13 hcase30 hcase32 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase331b hcase341a hcase341b hcase401a hcase020a hcase020b hcase140a hcase140b hcase411a hcase00 hcase04 hcase10 hcase13 hcase30 hcase32 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase301b hcase031a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase341a hcase341b hcase401a hcase020b hcase420b hcase430b hcase00 hcase04 hcase10 hcase13 hcase30 hcase32 hcase41 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase331b hcase341a hcase341b hcase401a hcase020a hcase020b hcase141a hcase141b hcase420a hcase420b hcase431a hcase00 hcase04 hcase10 hcase13 hcase30 hcase32 hcase41 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase331b hcase341a hcase341b hcase401a hcase020a hcase020b hcase141a hcase141b hcase421a hcase00 hcase04 hcase10 hcase13 hcase30 hcase32 hcase41 hcase43 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase110a hcase110b hcase331a hcase331b hcase341a hcase341b hcase401a hcase401b hcase021a hcase00 hcase04 hcase10 hcase13 hcase14 hcase30 hcase32 hcase41 hcase42 hcase43 hcase44
                    omega
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase140b hcase330b hcase320b hcase340b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase140b hcase330b hcase320b hcase341a hcase440b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase140b hcase330b hcase320b hcase341a hcase441a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43
                      omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase010a hcase010b hcase310b hcase120a hcase120b hcase111a hcase111b hcase140a hcase140b hcase330b hcase321a hcase400b hcase340b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase031a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111b hcase140a hcase140b hcase330b hcase321a hcase400b hcase341a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120b hcase111a hcase140b hcase330a hcase330b hcase321a hcase321b hcase401a hcase410b hcase440b hcase420b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase34 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase140a hcase140b hcase330a hcase330b hcase321a hcase321b hcase401a hcase410a hcase410b hcase440a hcase440b hcase421a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase34 hcase43
                          omega
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase310b hcase120a hcase120b hcase111a hcase140b hcase330b hcase321a hcase401a hcase401b hcase410a hcase410b hcase340b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hcut55 hcut70 hcut14 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040a hcase040b hcase301a hcase031a hcase010b hcase310a hcase310b hcase120b hcase111a hcase140b hcase330b hcase321a hcase401a hcase410b hcase441a hcase341a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase42 hcase43
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase140a hcase140b hcase330a hcase330b hcase321a hcase321b hcase401a hcase411a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase34 hcase42 hcase43 hcase44
                      omega
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase140b hcase331a hcase020a hcase020b hcase340b hcase400a hcase400b hcase320b hcase00 hcase04 hcase10 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310b hcase120a hcase120b hcase111a hcase111b hcase140a hcase140b hcase331a hcase020a hcase020b hcase340b hcase400b hcase321a hcase00 hcase04 hcase10 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase010b hcase310a hcase310b hcase120b hcase111a hcase140b hcase020a hcase020b hcase340a hcase340b hcase401a hcase410b hcase420b hcase430b hcase00 hcase04 hcase10 hcase13 hcase30 hcase32 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase140a hcase140b hcase331a hcase331b hcase020a hcase020b hcase340a hcase340b hcase401a hcase410a hcase410b hcase420a hcase420b hcase431a hcase00 hcase04 hcase10 hcase13 hcase30 hcase32 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase140a hcase140b hcase331a hcase331b hcase020a hcase020b hcase340a hcase340b hcase401a hcase410a hcase410b hcase421a hcase00 hcase04 hcase10 hcase13 hcase30 hcase32 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase140a hcase140b hcase331a hcase331b hcase020a hcase020b hcase340a hcase340b hcase401a hcase411a hcase00 hcase04 hcase10 hcase13 hcase30 hcase32 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase031a hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase140a hcase140b hcase331a hcase020a hcase020b hcase341a hcase341b hcase320a hcase320b hcase410b hcase400b hcase00 hcase04 hcase10 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase010b hcase310a hcase310b hcase120b hcase111a hcase140b hcase020a hcase020b hcase341a hcase341b hcase320a hcase320b hcase410b hcase401a hcase420b hcase430b hcase00 hcase04 hcase10 hcase13 hcase30 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase140a hcase140b hcase331a hcase331b hcase020a hcase020b hcase341a hcase341b hcase320a hcase320b hcase410a hcase410b hcase401a hcase420a hcase420b hcase431a hcase00 hcase04 hcase10 hcase13 hcase30 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase140a hcase140b hcase331a hcase331b hcase020a hcase020b hcase341a hcase341b hcase320a hcase320b hcase410a hcase410b hcase401a hcase421a hcase00 hcase04 hcase10 hcase13 hcase30 hcase43 hcase44
                            omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310b hcase120a hcase120b hcase111a hcase111b hcase140a hcase140b hcase331a hcase020b hcase341a hcase320b hcase00 hcase04 hcase10 hcase13 hcase30 hcase40 hcase42 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase140a hcase140b hcase331a hcase020a hcase020b hcase341a hcase321a hcase00 hcase04 hcase10 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase140a hcase140b hcase331a hcase331b hcase021a hcase00 hcase04 hcase10 hcase13 hcase30 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase031a hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111b hcase141b hcase400b hcase330b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase301b hcase031a hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111b hcase141b hcase400b hcase331a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase401a hcase330b hcase410b hcase420b hcase440b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase32 hcase34 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase301b hcase031a hcase010b hcase310a hcase310b hcase120b hcase111a hcase141a hcase401a hcase330b hcase410b hcase420b hcase441a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase32 hcase34 hcase43
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase141a hcase141b hcase401a hcase330a hcase330b hcase410a hcase410b hcase421a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase32 hcase34 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase141a hcase141b hcase401a hcase330a hcase330b hcase411a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase32 hcase34 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase301b hcase031a hcase010b hcase310a hcase310b hcase120b hcase111a hcase141a hcase401a hcase410b hcase420b hcase430b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase32 hcase34 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase141a hcase141b hcase401a hcase331a hcase331b hcase410a hcase410b hcase420a hcase420b hcase431a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase32 hcase34 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase141a hcase141b hcase401a hcase331a hcase331b hcase410a hcase410b hcase421a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase32 hcase34 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase120a hcase120b hcase111a hcase111b hcase141a hcase141b hcase401a hcase331a hcase331b hcase411a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase32 hcase34 hcase42 hcase43 hcase44
                    omega
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase310b hcase320b hcase330b hcase020a hcase020b hcase340b hcase00 hcase04 hcase10 hcase11 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310b hcase320b hcase330b hcase020b hcase341a hcase00 hcase04 hcase10 hcase11 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase010a hcase010b hcase310a hcase310b hcase121a hcase121b hcase320a hcase320b hcase330a hcase330b hcase021a hcase00 hcase04 hcase10 hcase11 hcase13 hcase14 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310b hcase320b hcase331a hcase020b hcase340b hcase00 hcase04 hcase10 hcase11 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310b hcase320b hcase331a hcase020b hcase341a hcase00 hcase04 hcase10 hcase11 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase010a hcase010b hcase310a hcase310b hcase121a hcase121b hcase320a hcase320b hcase331a hcase331b hcase021a hcase00 hcase04 hcase10 hcase11 hcase13 hcase14 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase031a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase340a hcase340b hcase400b hcase00 hcase02 hcase04 hcase10 hcase11 hcase13 hcase14 hcase30 hcase33 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase010a hcase010b hcase310b hcase121a hcase321a hcase340b hcase401a hcase401b hcase330b hcase140b hcase100b hcase110b hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          clear hn4 hsum_nat0 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase010a hcase010b hcase310b hcase121a hcase321a hcase340b hcase401a hcase330b hcase140b hcase100a hcase100b hcase111a hcase420b hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase121a hcase121b hcase321a hcase321b hcase340a hcase340b hcase401a hcase330a hcase330b hcase140a hcase140b hcase100a hcase100b hcase111a hcase111b hcase421a hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase43 hcase44
                          omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          clear hn4 hsum_nat0 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase310b hcase121a hcase321a hcase340b hcase401a hcase330b hcase140b hcase101a hcase110b hcase410b hcase00 hcase02 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase121a hcase121b hcase321a hcase321b hcase340a hcase340b hcase401a hcase330a hcase330b hcase140a hcase140b hcase101a hcase101b hcase110a hcase110b hcase411a hcase00 hcase02 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase121a hcase321a hcase321b hcase340a hcase340b hcase401a hcase401b hcase330a hcase330b hcase140a hcase140b hcase101a hcase111a hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut33 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase010a hcase010b hcase310b hcase121a hcase321a hcase340b hcase401a hcase330b hcase141a hcase100b hcase110b hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase121a hcase321a hcase321b hcase340a hcase340b hcase401a hcase401b hcase330a hcase330b hcase141a hcase100a hcase100b hcase111a hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase121a hcase321a hcase321b hcase340a hcase340b hcase401a hcase401b hcase330a hcase330b hcase141a hcase101a hcase00 hcase02 hcase04 hcase11 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310a hcase310b hcase121a hcase321a hcase340b hcase401a hcase420b hcase020b hcase430b hcase00 hcase04 hcase10 hcase11 hcase13 hcase14 hcase30 hcase41 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase121a hcase121b hcase321a hcase321b hcase340a hcase340b hcase401a hcase331a hcase331b hcase420a hcase420b hcase020a hcase020b hcase431a hcase00 hcase04 hcase10 hcase11 hcase13 hcase14 hcase30 hcase41 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase010a hcase010b hcase310a hcase310b hcase121a hcase121b hcase321a hcase321b hcase340a hcase340b hcase401a hcase401b hcase331a hcase331b hcase420a hcase420b hcase021a hcase00 hcase04 hcase10 hcase11 hcase13 hcase14 hcase30 hcase41 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase121a hcase121b hcase321a hcase321b hcase340a hcase340b hcase401a hcase331a hcase331b hcase421a hcase00 hcase02 hcase04 hcase10 hcase11 hcase13 hcase14 hcase30 hcase41 hcase43 hcase44
                    omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase031a hcase010b hcase310a hcase310b hcase321a hcase341a hcase140a hcase140b hcase400b hcase00 hcase02 hcase04 hcase10 hcase11 hcase13 hcase30 hcase33 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase121a hcase321a hcase321b hcase341a hcase341b hcase140b hcase401a hcase401b hcase330a hcase330b hcase100b hcase110b hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase121a hcase121b hcase321a hcase321b hcase140a hcase140b hcase401a hcase401b hcase330a hcase330b hcase100a hcase100b hcase111a hcase111b hcase440b hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase310b hcase121a hcase321a hcase341a hcase140b hcase401a hcase401b hcase330b hcase100a hcase100b hcase111a hcase441a hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43
                          omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase310b hcase121a hcase321a hcase341a hcase140b hcase401a hcase330b hcase101a hcase110b hcase410b hcase440b hcase00 hcase02 hcase04 hcase13 hcase30 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat4 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase310b hcase121a hcase321a hcase341a hcase140b hcase401a hcase401b hcase330b hcase101a hcase110a hcase110b hcase410a hcase410b hcase441a hcase00 hcase02 hcase04 hcase13 hcase30 hcase42 hcase43
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase121a hcase121b hcase321a hcase321b hcase341a hcase341b hcase140a hcase140b hcase401a hcase330a hcase330b hcase101a hcase101b hcase110a hcase110b hcase411a hcase00 hcase02 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase121a hcase321a hcase321b hcase341a hcase341b hcase140a hcase140b hcase401a hcase401b hcase330a hcase330b hcase101a hcase111a hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase121a hcase121b hcase321a hcase341a hcase140a hcase140b hcase401a hcase401b hcase331a hcase00 hcase02 hcase04 hcase10 hcase11 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase121a hcase121b hcase321a hcase321b hcase141a hcase141b hcase330a hcase330b hcase440b hcase00 hcase02 hcase04 hcase10 hcase11 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43
                    omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310b hcase321a hcase341a hcase141a hcase141b hcase330b hcase441a hcase400b hcase00 hcase02 hcase04 hcase10 hcase11 hcase13 hcase30 hcase41 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase310a hcase310b hcase121a hcase121b hcase321a hcase341a hcase330b hcase441a hcase401a hcase00 hcase02 hcase04 hcase10 hcase11 hcase13 hcase30 hcase41 hcase42 hcase43
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase310a hcase310b hcase121a hcase121b hcase321a hcase341a hcase141a hcase141b hcase331a hcase00 hcase02 hcase04 hcase10 hcase11 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
      ·
        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase330a hcase330b hcase320a hcase320b hcase120a hcase120b hcase340a hcase340b hcase100b hcase110b hcase140b hcase00 hcase02 hcase04 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase311a hcase330b hcase320b hcase120a hcase120b hcase340b hcase100b hcase110a hcase110b hcase141a hcase00 hcase02 hcase04 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase311a hcase330b hcase320b hcase120a hcase120b hcase340b hcase100b hcase111a hcase00 hcase02 hcase04 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase010a hcase010b hcase311a hcase330b hcase320b hcase120a hcase120b hcase340b hcase101a hcase140b hcase00 hcase02 hcase04 hcase11 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase311a hcase330b hcase320b hcase120a hcase120b hcase340b hcase101a hcase141a hcase00 hcase02 hcase04 hcase11 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase330a hcase330b hcase320a hcase320b hcase120a hcase120b hcase341a hcase341b hcase140b hcase100b hcase110b hcase00 hcase02 hcase04 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase311a hcase330b hcase320b hcase120a hcase120b hcase341a hcase140b hcase100a hcase100b hcase111a hcase00 hcase02 hcase04 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase311a hcase330b hcase320b hcase120a hcase120b hcase341a hcase140b hcase101a hcase00 hcase02 hcase04 hcase11 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase031a hcase010b hcase311a hcase330b hcase320a hcase320b hcase120a hcase120b hcase341a hcase141b hcase400b hcase00 hcase02 hcase04 hcase10 hcase11 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut32 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase330b hcase320a hcase320b hcase120b hcase341a hcase141a hcase401a hcase410b hcase00 hcase02 hcase04 hcase10 hcase11 hcase13 hcase30 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase330a hcase330b hcase320a hcase320b hcase120a hcase120b hcase341a hcase341b hcase141a hcase141b hcase401a hcase411a hcase00 hcase02 hcase04 hcase10 hcase11 hcase13 hcase30 hcase42 hcase43 hcase44
                      omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase330a hcase330b hcase320a hcase320b hcase121a hcase110b hcase100b hcase140b hcase00 hcase02 hcase04 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase311a hcase330b hcase320b hcase121a hcase110a hcase110b hcase100a hcase100b hcase141a hcase340b hcase00 hcase02 hcase04 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase031a hcase010b hcase311a hcase330b hcase320a hcase320b hcase110a hcase110b hcase100a hcase100b hcase141a hcase141b hcase341a hcase400b hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase031a hcase010b hcase311a hcase330b hcase320a hcase320b hcase121a hcase110b hcase100b hcase141a hcase341a hcase401a hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase311a hcase330b hcase320b hcase121a hcase110a hcase110b hcase101a hcase340b hcase00 hcase02 hcase04 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase311a hcase330b hcase320b hcase121a hcase110a hcase110b hcase101a hcase341a hcase140b hcase00 hcase02 hcase04 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase330a hcase330b hcase320a hcase320b hcase121a hcase110a hcase110b hcase101a hcase341a hcase341b hcase141a hcase00 hcase02 hcase04 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase311a hcase330b hcase320b hcase121a hcase111a hcase140b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase330a hcase330b hcase320a hcase320b hcase121a hcase111a hcase141a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
          ·
            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
            ·
              rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase031a hcase010b hcase311a hcase330b hcase321a hcase340a hcase340b hcase120a hcase120b hcase110a hcase110b hcase400b hcase00 hcase02 hcase04 hcase10 hcase13 hcase14 hcase30 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase330a hcase330b hcase321a hcase321b hcase340a hcase340b hcase120a hcase120b hcase110b hcase401a hcase401b hcase140b hcase100b hcase00 hcase02 hcase04 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          clear hn4 hcut55 hcut70 hcut14 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040a hcase040b hcase301a hcase031a hcase010b hcase330b hcase321a hcase340a hcase340b hcase120b hcase110a hcase110b hcase401a hcase140b hcase101a hcase410b hcase00 hcase02 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase330a hcase330b hcase321a hcase321b hcase340a hcase340b hcase120a hcase120b hcase110a hcase110b hcase401a hcase140a hcase140b hcase101a hcase101b hcase411a hcase00 hcase02 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut32 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase330b hcase321a hcase340a hcase340b hcase120b hcase110a hcase110b hcase401a hcase141a hcase410b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase330a hcase330b hcase321a hcase321b hcase340a hcase340b hcase120a hcase120b hcase110a hcase110b hcase401a hcase141a hcase141b hcase411a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase42 hcase43 hcase44
                        omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase031a hcase010b hcase311a hcase330b hcase321a hcase340a hcase340b hcase120a hcase120b hcase111b hcase400b hcase00 hcase02 hcase04 hcase10 hcase13 hcase14 hcase30 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut32 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase330b hcase321a hcase340a hcase340b hcase120b hcase111a hcase401a hcase410b hcase00 hcase02 hcase04 hcase10 hcase13 hcase14 hcase30 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase330a hcase330b hcase321a hcase321b hcase340a hcase340b hcase120a hcase120b hcase111a hcase111b hcase401a hcase411a hcase00 hcase02 hcase04 hcase10 hcase13 hcase14 hcase30 hcase42 hcase43 hcase44
                      omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase031a hcase010b hcase311a hcase330b hcase321a hcase340a hcase340b hcase121b hcase400b hcase00 hcase02 hcase04 hcase10 hcase11 hcase13 hcase14 hcase30 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase010a hcase010b hcase311a hcase330b hcase321a hcase340b hcase121a hcase401a hcase440b hcase00 hcase02 hcase04 hcase10 hcase11 hcase13 hcase14 hcase30 hcase41 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut29 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase311a hcase330b hcase321a hcase340b hcase121a hcase401a hcase441a hcase00 hcase02 hcase04 hcase10 hcase11 hcase13 hcase14 hcase30 hcase41 hcase42 hcase43
                    omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase311a hcase330a hcase330b hcase321a hcase341a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase331a hcase331b hcase110b hcase100b hcase140b hcase00 hcase02 hcase04 hcase12 hcase13 hcase30 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase031a hcase010b hcase311a hcase331a hcase110a hcase110b hcase100a hcase100b hcase020a hcase020b hcase120a hcase120b hcase400b hcase410b hcase00 hcase04 hcase13 hcase30 hcase32 hcase34 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase131b hcase040b hcase301a hcase031a hcase010b hcase311a hcase331a hcase110a hcase110b hcase100a hcase100b hcase141b hcase020a hcase020b hcase120a hcase120b hcase400b hcase411a hcase00 hcase04 hcase13 hcase30 hcase32 hcase34 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase311a hcase331a hcase110b hcase100b hcase020a hcase020b hcase120b hcase401a hcase410b hcase00 hcase04 hcase13 hcase30 hcase32 hcase34 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase331a hcase331b hcase110a hcase110b hcase100a hcase100b hcase141a hcase141b hcase020a hcase020b hcase120a hcase120b hcase401a hcase411a hcase00 hcase04 hcase13 hcase30 hcase32 hcase34 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase031a hcase010b hcase311a hcase331a hcase110a hcase110b hcase100a hcase100b hcase141a hcase141b hcase020a hcase020b hcase400b hcase00 hcase04 hcase13 hcase30 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut51 hcut34 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase031a hcase010b hcase311a hcase311b hcase331a hcase110b hcase100b hcase141a hcase020b hcase121a hcase401a hcase420b hcase00 hcase04 hcase13 hcase30 hcase32 hcase34 hcase41 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase331a hcase331b hcase110a hcase110b hcase100a hcase100b hcase141a hcase141b hcase020a hcase020b hcase121a hcase121b hcase401a hcase421a hcase00 hcase04 hcase13 hcase30 hcase32 hcase34 hcase41 hcase43 hcase44
                        omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase010a hcase010b hcase311a hcase311b hcase331a hcase331b hcase110a hcase110b hcase100a hcase100b hcase141a hcase141b hcase021a hcase00 hcase04 hcase12 hcase13 hcase30 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase311a hcase331a hcase110a hcase110b hcase340b hcase320b hcase400b hcase00 hcase02 hcase04 hcase12 hcase13 hcase14 hcase30 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase311a hcase331a hcase110a hcase110b hcase101a hcase340b hcase320b hcase401a hcase401b hcase410a hcase410b hcase140b hcase00 hcase02 hcase04 hcase12 hcase13 hcase30 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                        ·
                          clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase301b hcase031a hcase010a hcase010b hcase331a hcase110a hcase110b hcase101a hcase340a hcase340b hcase320a hcase320b hcase401a hcase410b hcase141a hcase120b hcase00 hcase02 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase331a hcase331b hcase110a hcase110b hcase101a hcase340a hcase340b hcase320a hcase320b hcase401a hcase401b hcase410a hcase410b hcase141a hcase121a hcase00 hcase02 hcase04 hcase13 hcase30 hcase42 hcase43 hcase44
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase331a hcase331b hcase110a hcase110b hcase101a hcase101b hcase340a hcase340b hcase320a hcase320b hcase401a hcase411a hcase00 hcase02 hcase04 hcase12 hcase13 hcase14 hcase30 hcase42 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase311a hcase331a hcase110a hcase110b hcase101a hcase101b hcase340a hcase340b hcase321a hcase00 hcase02 hcase04 hcase12 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase311a hcase331a hcase110a hcase110b hcase101a hcase101b hcase341a hcase00 hcase02 hcase04 hcase12 hcase13 hcase14 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase311a hcase331a hcase111a hcase120a hcase120b hcase140b hcase340b hcase320b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase311a hcase331a hcase111a hcase111b hcase120a hcase120b hcase140a hcase140b hcase340a hcase340b hcase321a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase311a hcase331a hcase111a hcase111b hcase120a hcase120b hcase140a hcase140b hcase341a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase311a hcase331a hcase120a hcase120b hcase141a hcase141b hcase320b hcase340b hcase400b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat3 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase301b hcase031a hcase010a hcase010b hcase331a hcase111a hcase120b hcase141a hcase320a hcase320b hcase340a hcase340b hcase401a hcase410b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase331a hcase331b hcase111a hcase111b hcase120a hcase120b hcase141a hcase141b hcase320a hcase320b hcase340a hcase340b hcase401a hcase411a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase42 hcase43 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase311a hcase331a hcase111a hcase111b hcase120a hcase120b hcase141a hcase141b hcase320a hcase320b hcase341a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase311a hcase331a hcase111a hcase111b hcase120a hcase120b hcase141a hcase141b hcase321a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut43 hcut1 hcut28 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase131a hcase040b hcase301a hcase031a hcase010b hcase311a hcase331a hcase111a hcase121a hcase140b hcase320b hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase031a hcase031b hcase010a hcase010b hcase311a hcase331a hcase111a hcase111b hcase121a hcase121b hcase140a hcase140b hcase321a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase131a hcase040a hcase040b hcase301a hcase301b hcase031a hcase031b hcase010a hcase010b hcase311a hcase311b hcase331a hcase331b hcase111a hcase121a hcase141a hcase00 hcase02 hcase04 hcase10 hcase13 hcase30 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut70 hcut14 hcut72 hcut53 hcut17 hcut22 hcut73 hcut42 hcut60 hcut7 hcut33 hcut64 hcut11 hcut59 hcut57 hcut37 hcut66 hcut23 hcut71 hcut32 hcut51 hcut5 hcut34 hcut2 hcut9 hcut50 hcut3 hcut43 hcut1 hcut28 hcut29 hcut0 hcut26 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase031a hcase011a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega

#print axioms symbolic_v2_mask15_integer_shard003
end Jsp404.SixExactFloorKernel
