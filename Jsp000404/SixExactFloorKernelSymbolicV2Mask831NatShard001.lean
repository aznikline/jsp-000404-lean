import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask831_integer_shard001 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut29 : (s01 + s34 + u01 + u34) + 1 ≤ (s44 + 2))
    (hcut65 : (s00 + s01 + s04 + s13 + s34 + u00 + u01 + u04 + u13 + u34) + 1 ≤ (2 * n))
    (hcut63 : (s30 + s33 + s41 + s42 + u30 + u33 + u41 + u42) + 1 ≤ (n))
    (hcut25 : (s10 + s43 + s44 + u10 + u43 + u44) + 1 ≤ (n + 1))
    (hcut44 : (s13 + s30 + u13 + u30 + 1) + 1 ≤ (n))
    (hcut35 : (s03 + s11 + s14 + s42 + u03 + u11 + u14 + u42 + 1) + 1 ≤ (n))
    (hcut61 : (s00 + s01 + s04 + s13 + s31 + s34 + u00 + u01 + u04 + u13 + u31 + u34) + 1 ≤ (2 * n + 1))
    (hcut55 : (s10 + s13 + s31 + s40 + s42 + s44 + u10 + u13 + u31 + u40 + u42 + u44) + 1 ≤ (2 * n + 1))
    (hcut2 : (s13 + s14 + s30 + s31 + u13 + u14 + u30 + u31) + 1 ≤ (n + 1))
    (hcut5 : (s10 + s11 + s42 + s43 + s44 + u10 + u11 + u42 + u43 + u44) + 1 ≤ (n + 2))
    (hcut45 : (s34 + s41 + s42 + u34 + u41 + u42) + 1 ≤ (n))
    (hcut51 : (s00 + s04 + s13 + s40 + s44 + u00 + u04 + u13 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut48 : (s14 + s30 + u14 + u30 + 1) + 1 ≤ (n))
    (hcut40 : (s14 + u14 + 2) + 1 ≤ (n))
    (hcut32 : (s02 + s10 + s14 + s42 + u02 + u10 + u14 + u42) + 1 ≤ (n + 1))
    (hcut70 : (s10 + s11 + s12 + s13 + u10 + u11 + u12 + u13) + 1 ≤ (n))
    (hcut50 : (s40 + s41 + s44 + u40 + u41 + u44) + 1 ≤ (n + 1))
    (hcut8 : (s12 + s41 + u12 + u41) + 1 ≤ (s31 + 2))
    (hcut47 : (s03 + s04 + s10 + s11 + u03 + u04 + u10 + u11) + 1 ≤ (n))
    (hcut26 : (s13 + s31 + u13 + u31 + 1) + 1 ≤ (n))
    (hcut20 : (s42 + s43 + u42 + u43 + 1) + 1 ≤ (n))
    (hcut66 : (s01 + s04 + s11 + u01 + u04 + u11) + 1 ≤ (n))
    (hcut46 : (s14 + s31 + u14 + u31 + 1) + 1 ≤ (n))
    (hcut57 : (s31 + s32 + s40 + u31 + u32 + u40 + 1) + 1 ≤ (n))
    (hcut11 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 2))
    (hcut59 : (s11 + s13 + s31 + s40 + s43 + s44 + u11 + u13 + u31 + u40 + u43 + u44) + 1 ≤ (2 * n + 1))
    (hcut49 : (s30 + u30 + 2) + 1 ≤ (n))
    (hcut41 : (s03 + u03 + 3) + 1 ≤ (n))
    (hcut6 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut43 : (s00 + s02 + s04 + u00 + u02 + u04) + 1 ≤ (n + 1))
    (hcut54 : (s30 + s33 + s34 + s42 + u30 + u33 + u34 + u42) + 1 ≤ (n + 1))
    (hcut0 : (s02 + s03 + s32 + s33 + u02 + u03 + u32 + u33) + 1 ≤ (s13 + 2))
    (hcut17 : (s40 + u40) + 1 ≤ (s30 + 2))
    (hcut36 : (s11 + s14 + s43 + u11 + u14 + u43) + 1 ≤ (n))
    (hcut23 : (s43 + s44 + u43 + u44) + 1 ≤ (n))
    (hcut18 : (s31 + s32 + u31 + u32 + 2) + 1 ≤ (n))
    (hcut62 : (s02 + s03 + s11 + s42 + u02 + u03 + u11 + u42 + 1) + 1 ≤ (n))
    (hcut52 : (s00 + s04 + s31 + s40 + s44 + u00 + u04 + u31 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut22 : (s01 + s13 + u01 + u13 + 4) + 1 ≤ (2 * n))
    (hcut33 : (s02 + s11 + s14 + s42 + u02 + u11 + u14 + u42) + 1 ≤ (n))
    (hcut42 : (s02 + s13 + u02 + u13 + 4) + 1 ≤ (2 * n))
    (hcut30 : (s42 + s43 + s44 + u42 + u43 + u44) + 1 ≤ (n + 1))
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
    (hcase001a : 1 ≤ s00)
    (hcase001b : u00 = 1)
    (hcase330a : s33 = 0)
    (hcase330b : u33 = 0)
    (hcase340a : s34 = 0)
    (hcase340b : u34 = 0)
    : False := by
  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
  ·
    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
    ·
      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
      ·
        clear hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase300b hcase310b hcase320b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase300b hcase310a hcase310b hcase321a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase300b hcase311a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega
  ·
    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
    ·
      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
      ·
        rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
        ·
          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase120b hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase320a hcase320b hcase130b hcase400a hcase400b hcase440a hcase440b hcase410a hcase410b hcase110b hcase00 hcase02 hcase14 hcase31 hcase33 hcase34 hcase42 hcase43
                          omega
                        ·
                          clear hsum_nat0 hsum_nat3 hcut29 hcut65 hcut63 hcut25 hcut44 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120b hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase320a hcase320b hcase130b hcase400b hcase440b hcase410b hcase111a hcase00 hcase02 hcase14 hcase31 hcase33 hcase34 hcase42 hcase43
                          omega
                      ·
                        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase120b hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase320a hcase320b hcase130b hcase400a hcase400b hcase440a hcase440b hcase411a hcase411b hcase110b hcase00 hcase02 hcase14 hcase31 hcase33 hcase34 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hcut29 hcut65 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase120b hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase320a hcase320b hcase130b hcase400b hcase440b hcase411a hcase111a hcase00 hcase02 hcase14 hcase31 hcase33 hcase34 hcase42 hcase43
                          omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase120b hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase320a hcase320b hcase130b hcase400a hcase400b hcase441a hcase441b hcase110b hcase00 hcase02 hcase14 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43
                        omega
                      ·
                        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase320a hcase320b hcase130b hcase400b hcase441a hcase111a hcase140b hcase430a hcase430b hcase410b hcase00 hcase02 hcase31 hcase33 hcase34 hcase42
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut29 hcut65 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase001a hcase330a hcase330b hcase340a hcase340b hcase120a hcase120b hcase100a hcase100b hcase010b hcase030b hcase040b hcase320a hcase320b hcase130a hcase130b hcase400b hcase441a hcase111a hcase111b hcase140a hcase140b hcase430b hcase411a hcase00 hcase02 hcase31 hcase33 hcase34 hcase42
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase320a hcase320b hcase130b hcase400a hcase400b hcase111a hcase140b hcase00 hcase02 hcase31 hcase33 hcase34 hcase41 hcase42
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120b hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase320a hcase320b hcase130b hcase400a hcase400b hcase441a hcase441b hcase111a hcase141a hcase00 hcase02 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43
                          omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase320b hcase130a hcase130b hcase401a hcase401b hcase310b hcase00 hcase02 hcase11 hcase14 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut29 hcut65 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase320a hcase320b hcase130a hcase130b hcase401a hcase311a hcase430b hcase440b hcase00 hcase02 hcase11 hcase14 hcase33 hcase34 hcase41 hcase42
                          omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut59 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase001a hcase330b hcase340b hcase301a hcase120b hcase100b hcase010b hcase030a hcase030b hcase040b hcase320a hcase320b hcase130b hcase401a hcase311a hcase430b hcase441a hcase410b hcase00 hcase02 hcase11 hcase14 hcase33 hcase34 hcase42
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase320a hcase320b hcase130a hcase130b hcase401a hcase311a hcase311b hcase430a hcase430b hcase441a hcase441b hcase411a hcase00 hcase02 hcase11 hcase14 hcase33 hcase34 hcase42
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase320a hcase320b hcase130a hcase130b hcase401a hcase311a hcase311b hcase431a hcase00 hcase02 hcase11 hcase14 hcase33 hcase34 hcase41 hcase42 hcase44
                        omega
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase320b hcase310b hcase00 hcase02 hcase11 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase320b hcase311a hcase00 hcase02 hcase11 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase120b hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase321a hcase321b hcase400a hcase400b hcase410a hcase410b hcase110b hcase130b hcase00 hcase02 hcase14 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase120b hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase321a hcase400a hcase400b hcase410a hcase410b hcase110b hcase131a hcase00 hcase02 hcase14 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase400a hcase400b hcase410a hcase410b hcase111a hcase111b hcase140a hcase140b hcase130b hcase00 hcase02 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase321a hcase400a hcase400b hcase410a hcase410b hcase111a hcase111b hcase140a hcase140b hcase131a hcase310b hcase00 hcase02 hcase33 hcase34 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase321a hcase400b hcase410b hcase111a hcase140b hcase131a hcase311a hcase00 hcase02 hcase33 hcase34 hcase42 hcase43 hcase44
                            omega
                      ·
                        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                        ·
                          clear hn4 hsum_nat3 hcut29 hcut65 hcut63 hcut25 hcut44 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase001a hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120b hcase100b hcase010b hcase030a hcase030b hcase040b hcase321a hcase321b hcase400b hcase410b hcase130b hcase00 hcase02 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase321a hcase400a hcase400b hcase410a hcase410b hcase111a hcase111b hcase131a hcase00 hcase02 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                          omega
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase400a hcase400b hcase411a hcase411b hcase130b hcase00 hcase02 hcase11 hcase14 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase321a hcase400a hcase400b hcase411a hcase411b hcase131a hcase310b hcase00 hcase02 hcase11 hcase14 hcase33 hcase34 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          clear hn4 hsum_nat1 hcut29 hcut65 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase001a hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase010b hcase030b hcase040b hcase321a hcase400b hcase411a hcase131a hcase131b hcase311a hcase430b hcase00 hcase02 hcase11 hcase14 hcase33 hcase34 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase321a hcase321b hcase400a hcase400b hcase411a hcase131a hcase131b hcase311a hcase311b hcase431a hcase00 hcase02 hcase11 hcase14 hcase33 hcase34 hcase42 hcase44
                          omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120b hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase321a hcase110b hcase130b hcase00 hcase02 hcase14 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120b hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase321a hcase110b hcase131a hcase00 hcase02 hcase14 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase401a hcase401b hcase111a hcase111b hcase140a hcase140b hcase310a hcase310b hcase130b hcase00 hcase02 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase321a hcase401a hcase401b hcase111a hcase111b hcase140a hcase140b hcase310b hcase131a hcase00 hcase02 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                          omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase401a hcase111a hcase140b hcase410b hcase130b hcase00 hcase02 hcase33 hcase34 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase321a hcase401a hcase111a hcase140b hcase311a hcase410b hcase131a hcase00 hcase02 hcase33 hcase34 hcase42 hcase43 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase321a hcase321b hcase401a hcase111a hcase111b hcase140a hcase140b hcase311a hcase311b hcase411a hcase00 hcase02 hcase13 hcase33 hcase34 hcase42 hcase43 hcase44
                          omega
                    ·
                      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase401a hcase401b hcase111a hcase111b hcase141a hcase141b hcase130b hcase00 hcase02 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase040a hcase040b hcase321a hcase401a hcase401b hcase111a hcase111b hcase131a hcase00 hcase02 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                        omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase320a hcase320b hcase130a hcase130b hcase140b hcase00 hcase02 hcase11 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase120b hcase100b hcase010a hcase010b hcase030a hcase030b hcase041a hcase041b hcase320a hcase320b hcase130b hcase141a hcase110b hcase00 hcase02 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120b hcase100b hcase010a hcase010b hcase030a hcase030b hcase041a hcase041b hcase320a hcase320b hcase130b hcase141a hcase111a hcase00 hcase02 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase320b hcase00 hcase02 hcase11 hcase14 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase321a hcase321b hcase140b hcase00 hcase02 hcase11 hcase13 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase041a hcase041b hcase141a hcase141b hcase130b hcase00 hcase02 hcase11 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase030a hcase030b hcase321a hcase141a hcase131a hcase00 hcase02 hcase11 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120b hcase100b hcase010a hcase010b hcase110b hcase130b hcase00 hcase02 hcase04 hcase14 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase120b hcase100b hcase010a hcase010b hcase110b hcase131a hcase00 hcase02 hcase04 hcase14 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase111a hcase111b hcase310b hcase00 hcase02 hcase04 hcase13 hcase14 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120b hcase100b hcase010a hcase010b hcase111a hcase311a hcase311b hcase130b hcase00 hcase02 hcase04 hcase14 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase010a hcase010b hcase111a hcase111b hcase311a hcase131a hcase00 hcase02 hcase04 hcase14 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
        ·
          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase011a hcase011b hcase310b hcase320b hcase00 hcase02 hcase03 hcase04 hcase11 hcase13 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase011a hcase011b hcase310a hcase310b hcase130b hcase00 hcase02 hcase03 hcase04 hcase11 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase011a hcase011b hcase310b hcase321a hcase131a hcase00 hcase02 hcase03 hcase04 hcase11 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase120b hcase100b hcase011a hcase011b hcase030a hcase030b hcase110b hcase00 hcase02 hcase04 hcase13 hcase14 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120b hcase100b hcase311a hcase311b hcase030a hcase030b hcase111a hcase140b hcase130b hcase00 hcase02 hcase04 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase011a hcase011b hcase311a hcase030a hcase030b hcase111a hcase111b hcase140a hcase140b hcase320b hcase00 hcase02 hcase04 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120b hcase100a hcase100b hcase011a hcase011b hcase311a hcase030a hcase030b hcase111a hcase140b hcase131a hcase321a hcase410b hcase400b hcase00 hcase02 hcase04 hcase33 hcase34 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120b hcase100a hcase100b hcase011a hcase011b hcase311a hcase030a hcase030b hcase111a hcase140b hcase131a hcase321a hcase410b hcase401a hcase00 hcase02 hcase04 hcase33 hcase34 hcase42 hcase43 hcase44
                          omega
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              clear hn4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut46 hcut57 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase001a hcase330b hcase340b hcase301a hcase120a hcase120b hcase100b hcase011a hcase311a hcase030b hcase111a hcase140a hcase140b hcase131a hcase321a hcase411a hcase430b hcase400b hcase420b hcase00 hcase02 hcase04 hcase33 hcase34 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase011a hcase011b hcase311a hcase311b hcase030a hcase030b hcase111a hcase111b hcase140a hcase140b hcase131a hcase131b hcase321a hcase321b hcase411a hcase430a hcase430b hcase400a hcase400b hcase421a hcase00 hcase02 hcase04 hcase33 hcase34 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase011a hcase011b hcase311a hcase311b hcase030a hcase030b hcase111a hcase111b hcase140a hcase140b hcase131a hcase131b hcase321a hcase321b hcase411a hcase430a hcase430b hcase401a hcase00 hcase02 hcase04 hcase33 hcase34 hcase42 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase011a hcase011b hcase311a hcase311b hcase030a hcase030b hcase111a hcase111b hcase140a hcase140b hcase131a hcase131b hcase321a hcase321b hcase411a hcase431a hcase00 hcase02 hcase04 hcase33 hcase34 hcase40 hcase42 hcase44
                          omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120b hcase100b hcase011a hcase011b hcase311a hcase311b hcase030a hcase030b hcase111a hcase141a hcase130b hcase00 hcase02 hcase04 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase100a hcase100b hcase011a hcase011b hcase311a hcase030a hcase030b hcase111a hcase111b hcase131a hcase00 hcase02 hcase04 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase100a hcase100b hcase011a hcase311a hcase311b hcase031a hcase00 hcase02 hcase04 hcase11 hcase13 hcase14 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
      ·
        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase110a hcase110b hcase320b hcase310b hcase00 hcase01 hcase02 hcase03 hcase04 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301b hcase120b hcase101a hcase130b hcase110b hcase320a hcase320b hcase311b hcase400b hcase420b hcase410b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hcut29 hcut65 hcut63 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase120b hcase101a hcase130a hcase130b hcase110b hcase320a hcase320b hcase400b hcase420b hcase410b hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase43 hcase44
                        omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut29 hcut65 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase110a hcase110b hcase320a hcase320b hcase311a hcase311b hcase400b hcase420a hcase420b hcase411a hcase440b hcase430b hcase00 hcase01 hcase02 hcase03 hcase04 hcase14 hcase33 hcase34
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase110a hcase110b hcase320a hcase320b hcase311a hcase311b hcase400a hcase400b hcase420a hcase420b hcase411a hcase440a hcase440b hcase431a hcase00 hcase01 hcase02 hcase03 hcase04 hcase14 hcase33 hcase34
                          omega
                      ·
                        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hcut29 hcut65 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase120b hcase101a hcase130b hcase110b hcase320a hcase320b hcase311a hcase311b hcase400b hcase420a hcase420b hcase411a hcase441a hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase110a hcase110b hcase320b hcase311a hcase400a hcase400b hcase420a hcase420b hcase411a hcase411b hcase441a hcase441b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase43
                          omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hcut29 hcut65 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase120b hcase101a hcase130b hcase110a hcase110b hcase320a hcase320b hcase311a hcase311b hcase400b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase110a hcase110b hcase320b hcase311a hcase400a hcase400b hcase421a hcase421b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase41 hcase43 hcase44
                      omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut29 hcut65 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase110a hcase110b hcase320a hcase320b hcase311a hcase401a hcase140a hcase140b hcase420a hcase420b hcase430b hcase440b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase41
                          omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hcut29 hcut65 hcut63 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120b hcase101a hcase130b hcase110b hcase320a hcase320b hcase401a hcase140b hcase420b hcase430a hcase430b hcase441a hcase410b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase110a hcase110b hcase320a hcase320b hcase311a hcase311b hcase401a hcase140a hcase140b hcase420a hcase420b hcase430a hcase430b hcase441a hcase441b hcase411a hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase110a hcase110b hcase320a hcase320b hcase311a hcase311b hcase401a hcase140a hcase140b hcase420a hcase420b hcase431a hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase41 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase110a hcase110b hcase320a hcase320b hcase311a hcase311b hcase401a hcase140a hcase140b hcase421a hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase41 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase110a hcase110b hcase320b hcase311a hcase401a hcase401b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                    omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase101a hcase101b hcase130b hcase110a hcase110b hcase00 hcase01 hcase02 hcase03 hcase04 hcase14 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut29 hcut65 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase111a hcase111b hcase320a hcase320b hcase140a hcase140b hcase430b hcase440b hcase400b hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase33 hcase34 hcase41 hcase42
                      omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase111a hcase111b hcase320b hcase140a hcase140b hcase430a hcase430b hcase440a hcase440b hcase401a hcase401b hcase310b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase41 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut29 hcut65 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase111a hcase111b hcase320a hcase320b hcase140a hcase140b hcase430b hcase440b hcase401a hcase311a hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase41 hcase42
                        omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase111a hcase111b hcase320b hcase140a hcase140b hcase430a hcase430b hcase441a hcase441b hcase410a hcase410b hcase310b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase40 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120b hcase101a hcase130b hcase111a hcase320a hcase320b hcase140b hcase430a hcase430b hcase441a hcase410b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase40 hcase42
                        omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hcut29 hcut65 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase120b hcase101a hcase130b hcase111a hcase320a hcase320b hcase140b hcase430a hcase430b hcase441a hcase411a hcase400b hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase33 hcase34 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase111a hcase111b hcase320a hcase320b hcase140a hcase140b hcase430a hcase430b hcase441a hcase441b hcase411a hcase401a hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase33 hcase34 hcase42
                        omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase130a hcase130b hcase320a hcase320b hcase140a hcase140b hcase431a hcase400b hcase410b hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase33 hcase34 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase111a hcase111b hcase320a hcase320b hcase140a hcase140b hcase431a hcase400a hcase400b hcase411a hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase33 hcase34 hcase42 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase111a hcase111b hcase320a hcase320b hcase140a hcase140b hcase431a hcase401a hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase33 hcase34 hcase41 hcase42 hcase44
                    omega
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase111a hcase111b hcase320b hcase310b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase101b hcase130a hcase130b hcase111a hcase111b hcase320b hcase311a hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase101a hcase101b hcase130b hcase111a hcase111b hcase00 hcase01 hcase02 hcase03 hcase04 hcase14 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase101b hcase320b hcase310b hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase101b hcase320b hcase311a hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase101b hcase131a hcase321a hcase140a hcase140b hcase110a hcase110b hcase310b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120b hcase101a hcase131a hcase321a hcase140b hcase110a hcase110b hcase311a hcase400b hcase410b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase131a hcase321a hcase140a hcase140b hcase110b hcase311a hcase400b hcase411a hcase420b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase101a hcase101b hcase131a hcase131b hcase321a hcase321b hcase140a hcase140b hcase110a hcase110b hcase311a hcase311b hcase400a hcase400b hcase411a hcase421a hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase43 hcase44
                        omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase120b hcase101a hcase131a hcase321a hcase140b hcase110a hcase110b hcase311a hcase401a hcase410b hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase101a hcase101b hcase131a hcase131b hcase321a hcase321b hcase140a hcase140b hcase110a hcase110b hcase311a hcase311b hcase401a hcase411a hcase00 hcase01 hcase02 hcase03 hcase04 hcase33 hcase34 hcase42 hcase43 hcase44
                      omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase101a hcase131a hcase321a hcase321b hcase140b hcase111a hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase120a hcase120b hcase101a hcase101b hcase131a hcase321a hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
    ·
      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
      ·
        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
        ·
          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301b hcase121a hcase110b hcase140b hcase100b hcase130b hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase121a hcase110b hcase140b hcase100b hcase131a hcase310b hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase121a hcase110b hcase140a hcase140b hcase100b hcase131a hcase311a hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase110a hcase110b hcase140a hcase140b hcase101a hcase101b hcase130a hcase130b hcase430a hcase430b hcase420a hcase420b hcase310b hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase34 hcase40 hcase41 hcase44
                    omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301b hcase110a hcase110b hcase140a hcase140b hcase101a hcase101b hcase130a hcase130b hcase430b hcase420b hcase311a hcase311b hcase400b hcase440b hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase34 hcase41
                        omega
                      ·
                        clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301b hcase121a hcase110b hcase140b hcase101a hcase130b hcase430a hcase430b hcase420b hcase311a hcase311b hcase400b hcase441a hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase34 hcase41
                        omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase110a hcase110b hcase140a hcase140b hcase101a hcase101b hcase130a hcase130b hcase430b hcase420b hcase311a hcase401a hcase440b hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase34 hcase41
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hcut29 hcut65 hcut63 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase110b hcase140b hcase101a hcase130b hcase430a hcase430b hcase420b hcase311a hcase401a hcase441a hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase34 hcase41
                        omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase110a hcase110b hcase140a hcase140b hcase101a hcase101b hcase130a hcase130b hcase430a hcase430b hcase421a hcase421b hcase440a hcase440b hcase310b hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase34 hcase40 hcase41
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hcut29 hcut65 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase121a hcase121b hcase110a hcase110b hcase140a hcase140b hcase101a hcase101b hcase130a hcase130b hcase430b hcase421a hcase440b hcase311a hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase34 hcase40 hcase41
                      omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301b hcase121a hcase110a hcase110b hcase140b hcase101a hcase130b hcase430a hcase430b hcase421a hcase441a hcase400b hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase32 hcase33 hcase34 hcase41
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase110a hcase110b hcase140a hcase140b hcase101a hcase101b hcase130a hcase130b hcase430a hcase430b hcase421a hcase441a hcase441b hcase401a hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase32 hcase33 hcase34 hcase41
                      omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301b hcase121a hcase110b hcase140b hcase101a hcase130b hcase431a hcase420b hcase400b hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase110a hcase110b hcase140a hcase140b hcase101a hcase101b hcase130a hcase130b hcase431a hcase420a hcase420b hcase401a hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase110a hcase110b hcase140a hcase140b hcase101a hcase101b hcase130a hcase130b hcase431a hcase421a hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase110a hcase110b hcase140b hcase101a hcase131a hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase110a hcase110b hcase141a hcase141b hcase310b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase13 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase121a hcase121b hcase110a hcase110b hcase311a hcase320b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase13 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase121a hcase121b hcase110a hcase110b hcase311a hcase321a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase13 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
      ·
        rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
        ·
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase111a hcase111b hcase010a hcase010b hcase040a hcase040b hcase320a hcase320b hcase310b hcase00 hcase02 hcase03 hcase10 hcase13 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase001a hcase330a hcase330b hcase340a hcase340b hcase301b hcase111a hcase111b hcase010b hcase040b hcase320a hcase320b hcase311a hcase311b hcase030b hcase400b hcase430b hcase420b hcase00 hcase02 hcase10 hcase13 hcase14 hcase33 hcase34 hcase41 hcase44
                        omega
                      ·
                        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                        ·
                          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                          ·
                            clear hn4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase001a hcase330a hcase330b hcase340a hcase340b hcase301b hcase121a hcase111a hcase010b hcase040b hcase320a hcase320b hcase311a hcase311b hcase030a hcase030b hcase400b hcase430b hcase421a hcase100b hcase130b hcase00 hcase02 hcase14 hcase33 hcase34 hcase41 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase121a hcase121b hcase111a hcase111b hcase010a hcase010b hcase040a hcase040b hcase320b hcase311a hcase030a hcase030b hcase400a hcase400b hcase430a hcase430b hcase421a hcase421b hcase100a hcase100b hcase00 hcase02 hcase14 hcase33 hcase34 hcase41 hcase44
                            omega
                        ·
                          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase111a hcase010a hcase010b hcase040a hcase040b hcase320a hcase320b hcase311a hcase311b hcase030a hcase030b hcase400a hcase400b hcase430a hcase430b hcase421a hcase421b hcase101a hcase140b hcase00 hcase02 hcase13 hcase33 hcase34 hcase41 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase111a hcase010a hcase010b hcase040a hcase040b hcase320a hcase320b hcase311a hcase311b hcase030a hcase030b hcase400a hcase400b hcase430a hcase430b hcase421a hcase421b hcase101a hcase141a hcase00 hcase02 hcase13 hcase33 hcase34 hcase41 hcase44
                            omega
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                        ·
                          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                              ·
                                clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301b hcase121a hcase111a hcase010a hcase010b hcase040a hcase040b hcase320a hcase320b hcase311a hcase311b hcase030a hcase030b hcase400b hcase431a hcase100b hcase140a hcase140b hcase130b hcase420b hcase440b hcase00 hcase02 hcase33 hcase34 hcase41
                                omega
                              ·
                                clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301b hcase121a hcase111a hcase010a hcase010b hcase040a hcase040b hcase320a hcase320b hcase311a hcase311b hcase030a hcase030b hcase400b hcase431a hcase100a hcase100b hcase140b hcase130b hcase420a hcase420b hcase441a hcase00 hcase02 hcase33 hcase34 hcase41
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase010a hcase010b hcase040a hcase040b hcase320a hcase320b hcase311a hcase311b hcase030a hcase030b hcase400a hcase400b hcase431a hcase100a hcase100b hcase140a hcase140b hcase130a hcase130b hcase421a hcase00 hcase02 hcase33 hcase34 hcase41 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase121a hcase121b hcase111a hcase111b hcase010a hcase010b hcase040a hcase040b hcase320b hcase311a hcase030a hcase030b hcase400a hcase400b hcase431a hcase431b hcase100a hcase100b hcase140a hcase140b hcase00 hcase02 hcase33 hcase34 hcase41 hcase42 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase121a hcase121b hcase111a hcase111b hcase010a hcase010b hcase040a hcase040b hcase320b hcase311a hcase030a hcase030b hcase400a hcase400b hcase431a hcase431b hcase100a hcase100b hcase00 hcase02 hcase13 hcase33 hcase34 hcase41 hcase42 hcase44
                          omega
                      ·
                        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase111a hcase010a hcase010b hcase040a hcase040b hcase320a hcase320b hcase311a hcase311b hcase030a hcase030b hcase400a hcase400b hcase431a hcase431b hcase101a hcase140b hcase00 hcase02 hcase13 hcase33 hcase34 hcase41 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase111a hcase010a hcase010b hcase040a hcase040b hcase320a hcase320b hcase311a hcase311b hcase030a hcase030b hcase400a hcase400b hcase431a hcase431b hcase101a hcase141a hcase00 hcase02 hcase13 hcase33 hcase34 hcase41 hcase42 hcase44
                          omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase001a hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase111a hcase111b hcase010b hcase040b hcase320a hcase320b hcase311a hcase030b hcase401a hcase420b hcase430b hcase00 hcase02 hcase10 hcase13 hcase14 hcase33 hcase34 hcase41 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase010a hcase010b hcase040a hcase040b hcase320a hcase320b hcase311a hcase311b hcase030a hcase030b hcase401a hcase420a hcase420b hcase431a hcase00 hcase02 hcase10 hcase13 hcase14 hcase33 hcase34 hcase41 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase010a hcase010b hcase040a hcase040b hcase320a hcase320b hcase311a hcase311b hcase030a hcase030b hcase401a hcase421a hcase00 hcase02 hcase10 hcase13 hcase14 hcase33 hcase34 hcase41 hcase43 hcase44
                      omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase010a hcase010b hcase040a hcase040b hcase320a hcase320b hcase311a hcase311b hcase130b hcase00 hcase02 hcase10 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340b hcase301a hcase121a hcase121b hcase111a hcase111b hcase010a hcase010b hcase040a hcase040b hcase320a hcase320b hcase311a hcase131a hcase00 hcase02 hcase10 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase130b hcase00 hcase02 hcase03 hcase10 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase111a hcase010a hcase010b hcase040a hcase040b hcase321a hcase321b hcase140b hcase131a hcase00 hcase02 hcase03 hcase10 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase130b hcase00 hcase02 hcase03 hcase10 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase111a hcase010a hcase010b hcase040a hcase040b hcase321a hcase321b hcase141a hcase131a hcase00 hcase02 hcase03 hcase10 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase111a hcase111b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase310b hcase00 hcase02 hcase03 hcase10 hcase14 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase010a hcase010b hcase130a hcase130b hcase311a hcase311b hcase320a hcase320b hcase140b hcase00 hcase02 hcase03 hcase10 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase121a hcase121b hcase111a hcase111b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase311a hcase320b hcase00 hcase02 hcase03 hcase10 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase010a hcase010b hcase041a hcase041b hcase130b hcase311a hcase311b hcase00 hcase02 hcase03 hcase10 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase010a hcase010b hcase131a hcase131b hcase140b hcase00 hcase02 hcase03 hcase10 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase111a hcase010a hcase010b hcase041a hcase041b hcase131a hcase141a hcase00 hcase02 hcase03 hcase10 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase111a hcase111b hcase011a hcase011b hcase140a hcase140b hcase100a hcase100b hcase130a hcase130b hcase030a hcase030b hcase430a hcase430b hcase310b hcase00 hcase02 hcase04 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
                      omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase140a hcase140b hcase100a hcase100b hcase130a hcase130b hcase030a hcase030b hcase430a hcase430b hcase311a hcase311b hcase400a hcase400b hcase440b hcase00 hcase02 hcase04 hcase32 hcase33 hcase34 hcase41 hcase42
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut46 hcut57 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase001a hcase330a hcase330b hcase340a hcase340b hcase301b hcase121a hcase111a hcase011a hcase140b hcase100b hcase130b hcase030b hcase430b hcase311a hcase311b hcase400b hcase441a hcase420b hcase00 hcase02 hcase04 hcase32 hcase33 hcase34 hcase41
                            omega
                          ·
                            clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301b hcase121a hcase111a hcase011a hcase011b hcase140b hcase100a hcase100b hcase130b hcase030a hcase030b hcase430a hcase430b hcase311a hcase311b hcase400b hcase441a hcase421a hcase00 hcase02 hcase04 hcase32 hcase33 hcase34 hcase41
                            omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hcut29 hcut65 hcut63 hcut25 hcut44 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase111a hcase011a hcase011b hcase140a hcase140b hcase100b hcase130b hcase030a hcase030b hcase430b hcase311a hcase401a hcase440b hcase00 hcase02 hcase04 hcase32 hcase33 hcase34 hcase41 hcase42
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat3 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut46 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase001a hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase111a hcase011a hcase140b hcase100b hcase130b hcase030b hcase430b hcase311a hcase401a hcase441a hcase420b hcase00 hcase02 hcase04 hcase32 hcase33 hcase34 hcase41
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase011a hcase011b hcase140a hcase140b hcase100a hcase100b hcase130a hcase130b hcase030a hcase030b hcase430a hcase430b hcase311a hcase311b hcase401a hcase441a hcase441b hcase421a hcase00 hcase02 hcase04 hcase32 hcase33 hcase34 hcase41
                            omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase140a hcase140b hcase100a hcase100b hcase130a hcase130b hcase030a hcase030b hcase431a hcase431b hcase400a hcase400b hcase440b hcase00 hcase02 hcase04 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat0 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301b hcase121a hcase111a hcase011a hcase011b hcase140b hcase100a hcase100b hcase130b hcase030a hcase030b hcase431a hcase400b hcase441a hcase00 hcase02 hcase04 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase011a hcase011b hcase140a hcase140b hcase100a hcase100b hcase130a hcase130b hcase030a hcase030b hcase431a hcase401a hcase00 hcase02 hcase04 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase011a hcase140a hcase140b hcase100a hcase100b hcase130a hcase130b hcase031a hcase00 hcase02 hcase04 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase111a hcase011a hcase011b hcase140b hcase100a hcase100b hcase131a hcase00 hcase02 hcase03 hcase04 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase111a hcase011a hcase011b hcase140b hcase101a hcase00 hcase02 hcase03 hcase04 hcase13 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase121a hcase121b hcase111a hcase111b hcase011a hcase011b hcase130a hcase130b hcase320b hcase310b hcase00 hcase02 hcase03 hcase04 hcase10 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330b hcase340b hcase301a hcase121a hcase121b hcase111a hcase111b hcase011a hcase011b hcase130a hcase130b hcase320b hcase311a hcase00 hcase02 hcase03 hcase04 hcase10 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase111a hcase111b hcase011a hcase011b hcase141a hcase141b hcase130b hcase00 hcase02 hcase03 hcase04 hcase10 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut29 hcut65 hcut63 hcut25 hcut44 hcut35 hcut61 hcut55 hcut2 hcut5 hcut45 hcut51 hcut48 hcut40 hcut32 hcut70 hcut50 hcut8 hcut47 hcut26 hcut20 hcut66 hcut46 hcut57 hcut11 hcut59 hcut49 hcut41 hcut6 hcut43 hcut54 hcut0 hcut17 hcut36 hcut23 hcut18 hcut62 hcut52 hcut22 hcut33 hcut42 hcut30 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase301a hcase301b hcase121a hcase111a hcase011a hcase011b hcase141a hcase131a hcase00 hcase02 hcase03 hcase04 hcase10 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega

#print axioms symbolic_v2_mask831_integer_shard001
end Jsp404.SixExactFloorKernel
