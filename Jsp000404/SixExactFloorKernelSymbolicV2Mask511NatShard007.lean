import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask511_integer_shard007 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut23 : (s04 + u04 + 3) + 1 ≤ (n))
    (hcut16 : (s12 + s13 + s31 + u12 + u13 + u31 + 2) + 1 ≤ (n))
    (hcut26 : (s30 + s34 + u30 + u34 + 1) + 1 ≤ (n))
    (hcut70 : (s00 + s01 + s03 + s14 + u00 + u01 + u03 + u14) + 1 ≤ (n + 2))
    (hcut13 : (s32 + u32 + 3) + 1 ≤ (n))
    (hcut76 : (s01 + s02 + s30 + s31 + u01 + u02 + u30 + u31) + 1 ≤ (n))
    (hcut89 : (s00 + s04 + s12 + s13 + s32 + s40 + s44 + u00 + u04 + u12 + u13 + u32 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut81 : (s01 + s04 + s10 + s30 + s31 + s32 + s34 + u01 + u04 + u10 + u30 + u31 + u32 + u34) + 1 ≤ (2 * n + 1))
    (hcut75 : (s02 + s10 + s11 + s33 + u02 + u10 + u11 + u33) + 1 ≤ (n))
    (hcut61 : (s13 + s30 + s31 + s32 + u13 + u30 + u31 + u32) + 1 ≤ (n))
    (hcut27 : (s30 + s33 + u30 + u33 + 2) + 1 ≤ (n))
    (hcut29 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut50 : (s12 + s13 + s31 + s32 + u12 + u13 + u31 + u32 + 1) + 1 ≤ (n))
    (hcut32 : (s30 + s34 + s43 + u30 + u34 + u43) + 1 ≤ (n))
    (hcut46 : (s02 + s14 + u02 + u14) + 1 ≤ (s34 + 2))
    (hcut77 : (s00 + s12 + s13 + s40 + s41 + s44 + u00 + u12 + u13 + u40 + u41 + u44) + 1 ≤ (2 * n + 1))
    (hcut78 : (s01 + s30 + s34 + u01 + u30 + u34) + 1 ≤ (n))
    (hcut65 : (s33 + s34 + u33 + u34 + 1) + 1 ≤ (n))
    (hcut73 : (s12 + s14 + s31 + s32 + u12 + u14 + u31 + u32 + 1) + 1 ≤ (n))
    (hcut25 : (s34 + s40 + u34 + u40) + 1 ≤ (n))
    (hcut88 : (s00 + s04 + s12 + s13 + s40 + s41 + s44 + u00 + u04 + u12 + u13 + u40 + u41 + u44) + 1 ≤ (2 * n + 2))
    (hcut18 : (s12 + s30 + s31 + s32 + u12 + u30 + u31 + u32 + 1) + 1 ≤ (n))
    (hcut12 : (s30 + s43 + u30 + u43) + 1 ≤ (n))
    (hcut86 : (s40 + s42 + s43 + s44 + u40 + u42 + u43 + u44) + 1 ≤ (n + 1))
    (hcut68 : (s11 + s34 + u11 + u34) + 1 ≤ (n))
    (hcut22 : (s03 + u03 + 3) + 1 ≤ (n))
    (hcut56 : (s32 + s33 + s40 + u32 + u33 + u40) + 1 ≤ (n))
    (hcut87 : (s10 + s11 + s14 + s33 + u10 + u11 + u14 + u33) + 1 ≤ (n + 1))
    (hcut9 : (s34 + s42 + s43 + u34 + u42 + u43) + 1 ≤ (n))
    (hcut17 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 2))
    (hcut35 : (s03 + s10 + u03 + u10) + 1 ≤ (n))
    (hcut57 : (s00 + s01 + s34 + u00 + u01 + u34) + 1 ≤ (n + 2))
    (hcut0 : (s11 + s30 + s31 + s33 + s34 + s42 + u11 + u30 + u31 + u33 + u34 + u42) + 1 ≤ (n + 1))
    (hcut37 : (s44 + u44) + 1 ≤ (s01 + s34 + 5))
    (hcut1 : (s32 + s40 + s41 + s43 + s44 + u32 + u40 + u41 + u43 + u44) + 1 ≤ (n + s11 + 3))
    (hcut6 : (s13 + s31 + s32 + u13 + u31 + u32 + 1) + 1 ≤ (n))
    (hcut59 : (s32 + s34 + s40 + s41 + u32 + u34 + u40 + u41) + 1 ≤ (n + 1))
    (hcut83 : (s00 + s04 + s13 + s32 + s40 + s44 + u00 + u04 + u13 + u32 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut40 : (s33 + s40 + s41 + u33 + u40 + u41 + 1) + 1 ≤ (n))
    (hcut45 : (s03 + s14 + s30 + s31 + s33 + u03 + u14 + u30 + u31 + u33) + 1 ≤ (n))
    (hcut2 : (s41 + u41) + 1 ≤ (s31 + 2))
    (hcut64 : (s01 + s03 + s10 + u01 + u03 + u10) + 1 ≤ (n))
    (hcut80 : (s02 + s03 + s10 + s14 + s43 + u02 + u03 + u10 + u14 + u43) + 1 ≤ (n + 1))
    (hcut51 : (s01 + s31 + s34 + s43 + u01 + u31 + u34 + u43) + 1 ≤ (n + 1))
    (hcut58 : (s32 + s40 + u32 + u40) + 1 ≤ (s10 + s11 + 5))
    (hcut74 : (s12 + s13 + s14 + s31 + s32 + u12 + u13 + u14 + u31 + u32) + 1 ≤ (n))
    (hcut33 : (s40 + s43 + s44 + u40 + u43 + u44) + 1 ≤ (n + 1))
    (hcut47 : (s03 + s12 + s14 + s31 + u03 + u12 + u14 + u31 + 1) + 1 ≤ (n))
    (hcut48 : (s02 + s03 + s04 + u02 + u03 + u04) + 1 ≤ (s34 + 2))
    (hcut49 : (s01 + s02 + s03 + s14 + u01 + u02 + u03 + u14) + 1 ≤ (n))
    (hcut44 : (s01 + s30 + s31 + s43 + u01 + u30 + u31 + u43) + 1 ≤ (n + 1))
    (hcut3 : (s10 + s43 + u10 + u43) + 1 ≤ (s00 + 2))
    (hcut66 : (s04 + s32 + s41 + u04 + u32 + u41 + 1) + 1 ≤ (n))
    (hcut15 : (s10 + s14 + s43 + u10 + u14 + u43) + 1 ≤ (n + 1))
    (hcut31 : (s01 + s10 + s34 + u01 + u10 + u34) + 1 ≤ (n + 2))
    (hcut85 : (s00 + s03 + s12 + s32 + s40 + s44 + u00 + u03 + u12 + u32 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut42 : (s01 + s03 + s14 + s31 + u01 + u03 + u14 + u31) + 1 ≤ (n))
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
    (hcase011a : 1 ≤ s01)
    (hcase011b : u01 = 1)
    : False := by
  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
  ·
    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
    ·
      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
      ·
        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
        ·
          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase000b hcase020b hcase130a hcase130b hcase120a hcase120b hcase330b hcase040b hcase030b hcase01 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase000a hcase000b hcase020a hcase020b hcase130a hcase130b hcase120a hcase120b hcase330a hcase330b hcase040a hcase040b hcase031a hcase01 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase000a hcase000b hcase020a hcase020b hcase130a hcase130b hcase120a hcase120b hcase330a hcase330b hcase041a hcase01 hcase03 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  clear hn4 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase000b hcase020b hcase130b hcase120b hcase140b hcase040b hcase110b hcase01 hcase03 hcase10 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase000a hcase000b hcase020a hcase020b hcase130b hcase120b hcase140b hcase040a hcase040b hcase111a hcase01 hcase03 hcase10 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase000a hcase000b hcase020a hcase020b hcase130a hcase130b hcase120a hcase120b hcase331a hcase331b hcase140a hcase140b hcase041a hcase01 hcase03 hcase10 hcase11 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase000b hcase020a hcase020b hcase130a hcase130b hcase120a hcase120b hcase331a hcase331b hcase040b hcase01 hcase03 hcase10 hcase11 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase000a hcase000b hcase020a hcase020b hcase130a hcase130b hcase120a hcase120b hcase331a hcase331b hcase141a hcase141b hcase041a hcase01 hcase03 hcase10 hcase11 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase000b hcase020b hcase130a hcase130b hcase040b hcase320b hcase330b hcase01 hcase03 hcase10 hcase11 hcase14 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut89 hcut81 hcut75 hcut61 hcut29 hcut50 hcut32 hcut46 hcut77 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase000b hcase020b hcase130a hcase130b hcase121a hcase121b hcase040b hcase320b hcase331a hcase030b hcase01 hcase10 hcase11 hcase14 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase000a hcase000b hcase020a hcase020b hcase130a hcase130b hcase121a hcase121b hcase040a hcase040b hcase320a hcase320b hcase331a hcase331b hcase031a hcase01 hcase10 hcase11 hcase14 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                clear hn4 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase000b hcase020b hcase130b hcase121a hcase040b hcase110b hcase01 hcase03 hcase10 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut65 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase000b hcase020b hcase130a hcase130b hcase040b hcase321a hcase111a hcase111b hcase330b hcase030b hcase01 hcase10 hcase14 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase000a hcase000b hcase020a hcase020b hcase130a hcase130b hcase121a hcase121b hcase040a hcase040b hcase321a hcase321b hcase111a hcase111b hcase330a hcase330b hcase031a hcase01 hcase10 hcase14 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    clear hn4 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut65 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase000b hcase020a hcase020b hcase130b hcase121a hcase040b hcase321a hcase111a hcase331a hcase030b hcase01 hcase10 hcase14 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase000a hcase000b hcase020a hcase020b hcase130a hcase130b hcase121a hcase121b hcase040a hcase040b hcase321a hcase321b hcase111a hcase111b hcase331a hcase331b hcase031a hcase01 hcase10 hcase14 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase000a hcase000b hcase020a hcase020b hcase130a hcase130b hcase121a hcase121b hcase041a hcase01 hcase03 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
      ·
        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                clear hn4 hsum_nat3 hsum_nat4 hcut23 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase000b hcase020b hcase131a hcase030a hcase030b hcase140b hcase110b hcase040b hcase01 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase000a hcase000b hcase020a hcase020b hcase131a hcase131b hcase030a hcase030b hcase140a hcase140b hcase110a hcase110b hcase041a hcase01 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase000b hcase020b hcase131a hcase131b hcase030b hcase140a hcase140b hcase111a hcase111b hcase330b hcase040b hcase01 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase000a hcase000b hcase020a hcase020b hcase131a hcase131b hcase030a hcase030b hcase140a hcase140b hcase111a hcase111b hcase330a hcase330b hcase041a hcase01 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase000b hcase020a hcase020b hcase131a hcase131b hcase030b hcase140a hcase140b hcase331a hcase040b hcase320b hcase01 hcase10 hcase12 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut32 hcut46 hcut77 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase000b hcase020a hcase020b hcase131a hcase030b hcase140b hcase111a hcase331a hcase040b hcase321a hcase01 hcase10 hcase12 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase000a hcase000b hcase020a hcase020b hcase131a hcase131b hcase030a hcase030b hcase140a hcase140b hcase111a hcase111b hcase331a hcase331b hcase041a hcase01 hcase10 hcase12 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase000b hcase020a hcase020b hcase131a hcase131b hcase030a hcase030b hcase040b hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase000a hcase000b hcase020a hcase020b hcase131a hcase131b hcase030a hcase030b hcase141a hcase141b hcase041a hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase000a hcase000b hcase020a hcase020b hcase131a hcase131b hcase031a hcase01 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase000a hcase000b hcase021a hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega
  ·
    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
    ·
      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
      ·
        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
        ·
          rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      clear hsum_nat0 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase120b hcase300a hcase300b hcase310a hcase310b hcase110b hcase100b hcase130b hcase01 hcase03 hcase04 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut23 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase120a hcase120b hcase300a hcase300b hcase310a hcase310b hcase110b hcase100b hcase131a hcase01 hcase03 hcase04 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase300b hcase310b hcase110a hcase110b hcase320b hcase330b hcase01 hcase03 hcase04 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase300a hcase300b hcase310b hcase110a hcase110b hcase101a hcase101b hcase320b hcase331a hcase01 hcase03 hcase04 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase120b hcase300a hcase300b hcase310a hcase310b hcase110b hcase101a hcase321a hcase321b hcase130b hcase01 hcase03 hcase04 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase300b hcase310b hcase110a hcase110b hcase101a hcase101b hcase321a hcase131a hcase131b hcase330b hcase01 hcase03 hcase04 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase300b hcase310a hcase310b hcase110a hcase110b hcase101a hcase321a hcase131a hcase331a hcase01 hcase03 hcase04 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase300b hcase310b hcase111a hcase111b hcase130a hcase130b hcase320b hcase330b hcase01 hcase03 hcase04 hcase10 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase120b hcase300a hcase300b hcase310a hcase310b hcase111a hcase130b hcase320a hcase320b hcase01 hcase03 hcase04 hcase10 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase120b hcase300b hcase310b hcase111a hcase130b hcase321a hcase01 hcase03 hcase04 hcase10 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase300b hcase310b hcase111a hcase111b hcase131a hcase131b hcase320b hcase330b hcase01 hcase03 hcase04 hcase10 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase300b hcase310b hcase131a hcase131b hcase320b hcase331a hcase01 hcase03 hcase04 hcase10 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase300b hcase310b hcase111a hcase111b hcase131a hcase131b hcase321a hcase330b hcase01 hcase03 hcase04 hcase10 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase300b hcase310a hcase310b hcase111a hcase131a hcase321a hcase331a hcase01 hcase03 hcase04 hcase10 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase120a hcase120b hcase300a hcase300b hcase110b hcase100b hcase01 hcase03 hcase04 hcase13 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase120b hcase300a hcase300b hcase311a hcase311b hcase110b hcase101a hcase130b hcase01 hcase03 hcase04 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase300b hcase311a hcase110a hcase110b hcase101a hcase131a hcase320b hcase01 hcase03 hcase04 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase300b hcase311a hcase110a hcase110b hcase101a hcase131a hcase321a hcase01 hcase03 hcase04 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase120a hcase120b hcase300a hcase300b hcase111a hcase320b hcase100b hcase01 hcase03 hcase04 hcase13 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase300b hcase311a hcase111a hcase320b hcase101a hcase01 hcase03 hcase04 hcase13 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase120a hcase120b hcase300a hcase300b hcase111a hcase321a hcase100b hcase01 hcase03 hcase04 hcase13 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase300b hcase311a hcase111a hcase321a hcase101a hcase01 hcase03 hcase04 hcase13 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase301a hcase330b hcase320b hcase01 hcase03 hcase04 hcase10 hcase11 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase301a hcase330b hcase321a hcase01 hcase03 hcase04 hcase10 hcase11 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase120a hcase120b hcase301a hcase331a hcase310b hcase320b hcase01 hcase03 hcase04 hcase10 hcase11 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase120b hcase310a hcase310b hcase321a hcase321b hcase130b hcase100b hcase01 hcase03 hcase04 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase120b hcase301a hcase301b hcase310a hcase310b hcase321a hcase321b hcase130b hcase101a hcase01 hcase03 hcase04 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase120b hcase331a hcase310a hcase310b hcase321a hcase131a hcase100b hcase01 hcase03 hcase04 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase120b hcase301a hcase331a hcase310a hcase310b hcase321a hcase131a hcase101a hcase01 hcase03 hcase04 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase120b hcase331a hcase100b hcase01 hcase03 hcase04 hcase11 hcase13 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase120b hcase301a hcase301b hcase311a hcase311b hcase101a hcase130b hcase01 hcase03 hcase04 hcase11 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase120b hcase301a hcase331a hcase311a hcase101a hcase131a hcase01 hcase03 hcase04 hcase11 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut23 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase121a hcase030a hcase030b hcase100b hcase110b hcase01 hcase04 hcase13 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase030a hcase030b hcase100a hcase100b hcase111a hcase111b hcase300b hcase330b hcase01 hcase04 hcase13 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase121a hcase030a hcase030b hcase100a hcase100b hcase111a hcase300b hcase331a hcase320b hcase01 hcase04 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase121a hcase030a hcase030b hcase100a hcase100b hcase111a hcase300b hcase331a hcase321a hcase01 hcase04 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase121a hcase030a hcase030b hcase100b hcase111a hcase130b hcase01 hcase04 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase121a hcase030a hcase030b hcase100b hcase111a hcase301a hcase131a hcase320b hcase01 hcase04 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340a hcase340b hcase020a hcase020b hcase121a hcase030a hcase030b hcase100b hcase111a hcase301a hcase131a hcase321a hcase01 hcase04 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          clear hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase121a hcase121b hcase030a hcase030b hcase101a hcase101b hcase130a hcase130b hcase320b hcase310b hcase300b hcase330b hcase01 hcase04 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase121a hcase121b hcase030a hcase030b hcase101a hcase101b hcase130a hcase130b hcase320b hcase310b hcase300a hcase300b hcase331a hcase01 hcase04 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase121a hcase121b hcase030a hcase030b hcase101a hcase101b hcase130a hcase130b hcase320b hcase310b hcase301a hcase01 hcase04 hcase11 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase121a hcase030a hcase030b hcase101a hcase130a hcase130b hcase320b hcase311a hcase300b hcase01 hcase04 hcase11 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase121a hcase030a hcase030b hcase101a hcase130b hcase320a hcase320b hcase311a hcase301a hcase01 hcase04 hcase11 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase030a hcase030b hcase101a hcase101b hcase130a hcase130b hcase321a hcase330b hcase01 hcase04 hcase11 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase121a hcase030a hcase030b hcase101a hcase130b hcase321a hcase331a hcase01 hcase04 hcase11 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase121a hcase030a hcase030b hcase101a hcase131a hcase040a hcase040b hcase300b hcase320b hcase01 hcase11 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut61 hcut27 hcut29 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140b hcase340b hcase020a hcase020b hcase121a hcase030a hcase030b hcase101a hcase131a hcase040a hcase040b hcase300b hcase321a hcase01 hcase11 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase121a hcase121b hcase030a hcase030b hcase101a hcase101b hcase131a hcase131b hcase040a hcase040b hcase301a hcase320b hcase310b hcase01 hcase11 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase121a hcase121b hcase030a hcase030b hcase101a hcase101b hcase131a hcase131b hcase040a hcase040b hcase301a hcase320b hcase311a hcase330b hcase01 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase121a hcase121b hcase030a hcase030b hcase101a hcase101b hcase131a hcase131b hcase040a hcase040b hcase301a hcase320b hcase311a hcase331a hcase01 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                            omega
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase030a hcase030b hcase101a hcase101b hcase131a hcase131b hcase040a hcase040b hcase301a hcase321a hcase330b hcase01 hcase11 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                          ·
                            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                                ·
                                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                                  ·
                                    clear hn4 hsum_nat0 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut29 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase140b hcase340b hcase020a hcase020b hcase121a hcase030a hcase030b hcase101a hcase131a hcase040a hcase040b hcase301a hcase321a hcase331a hcase110b hcase310a hcase310b hcase400b hcase410b hcase420b hcase01 hcase43 hcase44
                                    omega
                                  ·
                                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                                    ·
                                      clear hn4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut35 hcut57 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase001a hcase140b hcase340a hcase340b hcase020b hcase121a hcase030a hcase030b hcase101a hcase131a hcase040b hcase301a hcase321a hcase331a hcase110a hcase110b hcase310a hcase310b hcase400b hcase410b hcase421a hcase430b hcase01 hcase44
                                      omega
                                    ·
                                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340a hcase340b hcase020a hcase020b hcase121a hcase121b hcase030a hcase030b hcase101a hcase101b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase321a hcase321b hcase331a hcase331b hcase110a hcase110b hcase310a hcase310b hcase400a hcase400b hcase410a hcase410b hcase421a hcase431a hcase01 hcase44
                                      omega
                                ·
                                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340a hcase340b hcase020a hcase020b hcase121a hcase121b hcase030a hcase030b hcase101a hcase101b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase321a hcase321b hcase331a hcase331b hcase110a hcase110b hcase310b hcase400a hcase400b hcase01 hcase42 hcase43 hcase44
                                  omega
                              ·
                                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                                ·
                                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                                  ·
                                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                                    ·
                                      clear hn4 hsum_nat0 hsum_nat1 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut12 hcut86 hcut68 hcut22 hcut87 hcut9 hcut17 hcut35 hcut57 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340b hcase020a hcase020b hcase030a hcase030b hcase101a hcase101b hcase131a hcase131b hcase040a hcase040b hcase301a hcase321a hcase331a hcase110a hcase110b hcase310a hcase310b hcase401a hcase410b hcase430b hcase440b hcase01 hcase42
                                      omega
                                    ·
                                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                                      ·
                                        clear hn4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut81 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase001a hcase140b hcase340b hcase020a hcase020b hcase121a hcase030b hcase101a hcase131a hcase040a hcase040b hcase301a hcase321a hcase331a hcase110a hcase110b hcase310a hcase310b hcase401a hcase410b hcase430b hcase441a hcase420b hcase01
                                        omega
                                      ·
                                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340a hcase340b hcase020a hcase020b hcase121a hcase121b hcase030a hcase030b hcase101a hcase101b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase321a hcase321b hcase331a hcase331b hcase110a hcase110b hcase310a hcase310b hcase401a hcase410a hcase410b hcase430a hcase430b hcase441a hcase441b hcase421a hcase01
                                        omega
                                  ·
                                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340a hcase340b hcase020a hcase020b hcase121a hcase121b hcase030a hcase030b hcase101a hcase101b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase321a hcase321b hcase331a hcase331b hcase110a hcase110b hcase310a hcase310b hcase401a hcase410a hcase410b hcase431a hcase01 hcase42 hcase44
                                    omega
                                ·
                                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340a hcase340b hcase020a hcase020b hcase121a hcase121b hcase030a hcase030b hcase101a hcase101b hcase131a hcase131b hcase040a hcase040b hcase301a hcase301b hcase321a hcase321b hcase331a hcase331b hcase110a hcase110b hcase310a hcase310b hcase401a hcase411a hcase01 hcase42 hcase43 hcase44
                                  omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340a hcase340b hcase020a hcase020b hcase121a hcase121b hcase030a hcase030b hcase101a hcase101b hcase131a hcase131b hcase040a hcase040b hcase301a hcase321a hcase331a hcase110a hcase110b hcase311a hcase01 hcase40 hcase41 hcase42 hcase43 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase001a hcase001b hcase140a hcase140b hcase340a hcase340b hcase020a hcase020b hcase121a hcase030a hcase030b hcase101a hcase131a hcase040a hcase040b hcase301a hcase301b hcase321a hcase321b hcase331a hcase331b hcase111a hcase01 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                            omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase001a hcase001b hcase140a hcase140b hcase340a hcase340b hcase020a hcase020b hcase121a hcase121b hcase030a hcase030b hcase101a hcase101b hcase131a hcase131b hcase041a hcase01 hcase11 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase001a hcase001b hcase140a hcase140b hcase340a hcase340b hcase020a hcase020b hcase121a hcase121b hcase031a hcase01 hcase04 hcase10 hcase11 hcase13 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase001a hcase001b hcase140a hcase140b hcase340a hcase340b hcase021a hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
        ·
          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase001a hcase140a hcase140b hcase020b hcase030b hcase040b hcase01 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase001a hcase001b hcase140a hcase140b hcase341a hcase341b hcase020a hcase020b hcase030a hcase030b hcase041a hcase01 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase001a hcase001b hcase140a hcase140b hcase341a hcase341b hcase020a hcase020b hcase031a hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase001a hcase001b hcase140a hcase140b hcase341a hcase341b hcase021a hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
    ·
      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
      ·
        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
        ·
          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase001a hcase040b hcase020b hcase01 hcase03 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase001a hcase001b hcase141a hcase141b hcase040a hcase040b hcase021a hcase01 hcase03 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut23 hcut16 hcut26 hcut70 hcut13 hcut76 hcut89 hcut81 hcut75 hcut61 hcut27 hcut29 hcut50 hcut32 hcut46 hcut77 hcut78 hcut65 hcut73 hcut25 hcut88 hcut18 hcut12 hcut86 hcut68 hcut22 hcut56 hcut87 hcut9 hcut17 hcut35 hcut57 hcut0 hcut37 hcut1 hcut6 hcut59 hcut83 hcut40 hcut45 hcut2 hcut64 hcut80 hcut51 hcut58 hcut74 hcut33 hcut47 hcut48 hcut49 hcut44 hcut3 hcut66 hcut15 hcut31 hcut85 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase001a hcase001b hcase141a hcase141b hcase041a hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega

#print axioms symbolic_v2_mask511_integer_shard007
end Jsp404.SixExactFloorKernel
