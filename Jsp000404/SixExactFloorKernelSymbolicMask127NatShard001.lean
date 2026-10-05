import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_mask127_integer_shard001 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut55 : (s30 + s32 + s33 + u30 + u32 + u33) + 1 ≤ (n))
    (hcut4 : (s02 + s03 + s10 + s14 + s32 + s33 + u02 + u03 + u10 + u14 + u32 + u33) + 1 ≤ (n + 1))
    (hcut46 : (s02 + s03 + s32 + u02 + u03 + u32 + 1) + 1 ≤ (n))
    (hcut52 : (s04 + s11 + s33 + u04 + u11 + u33 + 1) + 1 ≤ (n))
    (hcut53 : (s02 + s11 + s14 + u02 + u11 + u14 + 2) + 1 ≤ (n))
    (hcut8 : (s03 + u03) + 1 ≤ (s13 + 1))
    (hcut32 : (s30 + s32 + s34 + u30 + u32 + u34) + 1 ≤ (n))
    (hcut26 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut31 : (s31 + u31) + 1 ≤ (s10 + 1))
    (hcut48 : (s03 + s32 + s33 + u03 + u32 + u33 + 1) + 1 ≤ (n))
    (hcut58 : (s40 + s41 + s43 + s44 + u40 + u41 + u43 + u44) + 1 ≤ (n + 1))
    (hcut15 : (s40 + s41 + s42 + s43 + u40 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut59 : (s33 + s34 + s40 + s42 + u33 + u34 + u40 + u42) + 1 ≤ (n + 1))
    (hcut36 : (s01 + s30 + s34 + u01 + u30 + u34 + 1) + 1 ≤ (n))
    (hcut21 : (s03 + s32 + u03 + u32 + 2) + 1 ≤ (n))
    (hcut35 : (s30 + s31 + s33 + u30 + u31 + u33 + 1) + 1 ≤ (n))
    (hcut30 : (s34 + s40 + u34 + u40) + 1 ≤ (n))
    (hcut40 : (s02 + u02) + 1 ≤ (s34 + 1))
    (hcut27 : (s03 + s33 + u03 + u33 + 3) + 1 ≤ (n))
    (hcut13 : (s40 + s41 + s43 + u40 + u41 + u43) + 1 ≤ (n))
    (hcut50 : (s43 + s44 + u43 + u44 + 1) + 1 ≤ (n))
    (hcut16 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 2))
    (hcut22 : (s10 + s32 + u10 + u32 + 1) + 1 ≤ (n))
    (hcut33 : (s30 + s34 + u30 + u34 + 2) + 1 ≤ (n))
    (hcut51 : (s12 + s13 + s14 + u12 + u13 + u14 + 1) + 1 ≤ (n))
    (hcut0 : (s11 + s12 + s41 + s42 + u11 + u12 + u41 + u42) + 1 ≤ (s32 + 2))
    (hcut3 : (s00 + s04 + s13 + s40 + s44 + u00 + u04 + u13 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut45 : (s01 + s43 + u01 + u43) + 1 ≤ (s33 + 2))
    (hcut23 : (s14 + s32 + u14 + u32 + 1) + 1 ≤ (n))
    (hcut60 : (s40 + s41 + s42 + s44 + u40 + u41 + u42 + u44) + 1 ≤ (n + 1))
    (hcut42 : (s30 + s31 + u30 + u31) + 1 ≤ (s10 + 2))
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
    (hcase130a : s13 = 0)
    (hcase130b : u13 = 0)
    : False := by
  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
  ·
    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
    ·
      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
      ·
        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
        ·
          rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase100b hcase120b hcase110b hcase140b hcase00 hcase01 hcase03 hcase13 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase100b hcase120b hcase110a hcase110b hcase141a hcase00 hcase01 hcase03 hcase13 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase100b hcase120b hcase111a hcase00 hcase01 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase100a hcase100b hcase320b hcase00 hcase01 hcase03 hcase11 hcase13 hcase14 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase100b hcase121a hcase321a hcase140b hcase00 hcase01 hcase03 hcase11 hcase13 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase100b hcase121a hcase321a hcase141a hcase00 hcase01 hcase03 hcase11 hcase13 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase300b hcase310b hcase340b hcase00 hcase01 hcase03 hcase11 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase101b hcase300a hcase300b hcase310b hcase341a hcase320b hcase00 hcase01 hcase03 hcase11 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase300a hcase300b hcase310a hcase310b hcase341a hcase341b hcase140b hcase120b hcase110b hcase00 hcase01 hcase03 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase300a hcase300b hcase310a hcase310b hcase341a hcase341b hcase321a hcase140b hcase120a hcase120b hcase111a hcase00 hcase01 hcase03 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase300a hcase300b hcase310a hcase310b hcase341a hcase341b hcase321a hcase140b hcase121a hcase00 hcase01 hcase03 hcase11 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                      ·
                        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase300a hcase300b hcase310a hcase310b hcase341a hcase341b hcase141a hcase400a hcase400b hcase120b hcase110b hcase00 hcase01 hcase03 hcase13 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut55 hcut46 hcut52 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut33 hcut51 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase300a hcase300b hcase310a hcase310b hcase341a hcase341b hcase141a hcase400b hcase120b hcase111a hcase00 hcase01 hcase03 hcase13 hcase41 hcase42 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130a hcase130b hcase040b hcase020a hcase020b hcase330a hcase330b hcase300a hcase300b hcase310a hcase310b hcase341a hcase341b hcase321a hcase400b hcase00 hcase01 hcase03 hcase11 hcase13 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                        ·
                          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase300a hcase300b hcase310a hcase310b hcase341a hcase341b hcase141a hcase401a hcase401b hcase430a hcase430b hcase120b hcase110b hcase00 hcase01 hcase03 hcase13 hcase41 hcase42 hcase44
                            omega
                          ·
                            clear hn4 hcut55 hcut46 hcut52 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase300b hcase310b hcase341a hcase321a hcase401a hcase430a hcase430b hcase120b hcase111a hcase00 hcase01 hcase03 hcase13 hcase41 hcase42 hcase44
                            omega
                        ·
                          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                          ·
                            clear hn4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase020a hcase020b hcase330a hcase330b hcase300b hcase310b hcase341a hcase321a hcase401a hcase430b hcase121a hcase010b hcase00 hcase03 hcase11 hcase13 hcase41 hcase42 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase101b hcase300a hcase300b hcase310a hcase310b hcase341a hcase341b hcase321a hcase321b hcase141a hcase141b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase00 hcase03 hcase11 hcase13 hcase41 hcase42 hcase44
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase101b hcase300a hcase300b hcase310a hcase310b hcase341a hcase341b hcase321a hcase321b hcase141a hcase141b hcase401a hcase401b hcase00 hcase01 hcase03 hcase11 hcase12 hcase13 hcase41 hcase42 hcase44
                        omega
            ·
              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase300b hcase311a hcase010a hcase010b hcase430a hcase430b hcase340b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase44
                    omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase101b hcase300a hcase300b hcase311b hcase010a hcase010b hcase430b hcase341b hcase320a hcase320b hcase440b hcase400b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase41 hcase42
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase101b hcase300a hcase300b hcase311a hcase311b hcase010a hcase010b hcase430b hcase320b hcase440b hcase401a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase41 hcase42
                          omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase101b hcase300a hcase300b hcase311a hcase311b hcase010a hcase010b hcase430a hcase430b hcase341a hcase341b hcase320a hcase320b hcase441a hcase410b hcase420b hcase400b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase020b hcase330a hcase330b hcase101a hcase101b hcase300a hcase300b hcase311a hcase311b hcase010b hcase430b hcase320a hcase320b hcase441a hcase410b hcase420b hcase401a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase101b hcase300a hcase300b hcase311a hcase311b hcase010a hcase010b hcase430a hcase430b hcase341a hcase341b hcase320b hcase441a hcase441b hcase410a hcase410b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase40
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase101b hcase300a hcase300b hcase311a hcase311b hcase010a hcase010b hcase430a hcase430b hcase341a hcase341b hcase320b hcase441a hcase441b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase40 hcase42
                          omega
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                        ·
                          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase300a hcase300b hcase311a hcase311b hcase010a hcase010b hcase430a hcase430b hcase341a hcase341b hcase140b hcase120b hcase110b hcase00 hcase03 hcase13 hcase40 hcase41 hcase42 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase300a hcase300b hcase311a hcase311b hcase010a hcase010b hcase430a hcase430b hcase341a hcase341b hcase321a hcase140b hcase120a hcase120b hcase111a hcase00 hcase03 hcase13 hcase40 hcase41 hcase42 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase300a hcase300b hcase311a hcase311b hcase010a hcase010b hcase430a hcase430b hcase341a hcase341b hcase321a hcase140b hcase121a hcase00 hcase03 hcase11 hcase13 hcase40 hcase41 hcase42 hcase44
                          omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase020b hcase330a hcase330b hcase101a hcase300a hcase300b hcase010b hcase430b hcase341a hcase341b hcase321a hcase141a hcase141b hcase400b hcase00 hcase03 hcase11 hcase12 hcase13 hcase41 hcase42 hcase44
                          omega
                        ·
                          rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                          ·
                            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase300a hcase300b hcase311a hcase311b hcase010a hcase010b hcase430a hcase430b hcase341a hcase341b hcase141a hcase401a hcase401b hcase120b hcase110b hcase00 hcase03 hcase13 hcase41 hcase42 hcase44
                              omega
                            ·
                              clear hn4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase300b hcase311a hcase010b hcase430b hcase341a hcase321a hcase141a hcase401a hcase120a hcase120b hcase111a hcase00 hcase03 hcase13 hcase41 hcase42 hcase44
                              omega
                          ·
                            clear hn4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase300b hcase311a hcase010b hcase430b hcase341a hcase321a hcase401a hcase121a hcase00 hcase03 hcase11 hcase13 hcase41 hcase42 hcase44
                            omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase101b hcase300a hcase300b hcase311a hcase311b hcase010a hcase010b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase32 hcase34 hcase40 hcase41 hcase42 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase101b hcase300a hcase300b hcase311a hcase311b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase101b hcase301a hcase010a hcase010b hcase340a hcase340b hcase310b hcase320b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase301a hcase010a hcase010b hcase340b hcase310a hcase310b hcase321a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase301a hcase010a hcase010b hcase340b hcase311a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase101b hcase010a hcase010b hcase320a hcase320b hcase440b hcase410b hcase420b hcase400b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase101b hcase301a hcase301b hcase010a hcase010b hcase320a hcase320b hcase440b hcase410b hcase420b hcase401a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase43
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase101b hcase301a hcase301b hcase010a hcase010b hcase341a hcase341b hcase320b hcase440a hcase440b hcase410a hcase410b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase101b hcase301a hcase301b hcase010a hcase010b hcase341a hcase341b hcase320b hcase440a hcase440b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                      omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase101b hcase301a hcase301b hcase010a hcase010b hcase341a hcase341b hcase320a hcase320b hcase441a hcase410b hcase420b hcase400b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase43
                          omega
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase020b hcase330a hcase330b hcase101a hcase101b hcase301a hcase301b hcase010b hcase320a hcase320b hcase441a hcase410b hcase420b hcase401a hcase430b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase101b hcase301a hcase301b hcase010a hcase010b hcase341a hcase341b hcase320a hcase320b hcase441a hcase410a hcase410b hcase420b hcase401a hcase431a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase101b hcase301a hcase301b hcase010a hcase010b hcase341a hcase341b hcase320b hcase441a hcase441b hcase410a hcase410b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase101b hcase301a hcase301b hcase010a hcase010b hcase341a hcase341b hcase320b hcase441a hcase441b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                      omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase301a hcase301b hcase010a hcase010b hcase341a hcase341b hcase140b hcase120b hcase110b hcase00 hcase03 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase301a hcase301b hcase010a hcase010b hcase341a hcase341b hcase321a hcase140b hcase120a hcase120b hcase111a hcase00 hcase03 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase301a hcase301b hcase010a hcase010b hcase341a hcase341b hcase321a hcase140b hcase121a hcase00 hcase03 hcase11 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase101b hcase301a hcase010a hcase010b hcase341a hcase321a hcase141a hcase141b hcase310b hcase00 hcase03 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut33 hcut51 hcut3 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase020b hcase330b hcase101a hcase010a hcase010b hcase341a hcase341b hcase321a hcase141a hcase141b hcase400b hcase00 hcase03 hcase11 hcase12 hcase13 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                        ·
                          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase301a hcase301b hcase010a hcase010b hcase341a hcase341b hcase141a hcase311a hcase311b hcase401a hcase401b hcase120b hcase110b hcase00 hcase03 hcase13 hcase41 hcase42 hcase43 hcase44
                            omega
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              clear hn4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase301a hcase010b hcase341a hcase321a hcase141a hcase311a hcase401a hcase120a hcase120b hcase111a hcase430b hcase00 hcase03 hcase13 hcase41 hcase42 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase101b hcase301a hcase301b hcase010a hcase010b hcase341a hcase341b hcase321a hcase321b hcase141a hcase141b hcase311a hcase311b hcase401a hcase401b hcase120a hcase120b hcase111a hcase111b hcase00 hcase03 hcase13 hcase41 hcase42 hcase44
                              omega
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            clear hn4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase020a hcase020b hcase330a hcase330b hcase101a hcase301a hcase010b hcase341a hcase321a hcase311a hcase401a hcase121a hcase430b hcase00 hcase03 hcase11 hcase13 hcase41 hcase42 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase101b hcase301a hcase301b hcase010a hcase010b hcase341a hcase341b hcase321a hcase321b hcase141a hcase141b hcase311a hcase311b hcase401a hcase401b hcase121a hcase121b hcase00 hcase03 hcase11 hcase13 hcase41 hcase42 hcase44
                            omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase330b hcase101a hcase101b hcase301a hcase301b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
      ·
        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
        ·
          rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase110b hcase120b hcase100b hcase140b hcase00 hcase01 hcase03 hcase13 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase331a hcase331b hcase110a hcase110b hcase120b hcase100b hcase141a hcase00 hcase01 hcase03 hcase13 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase110b hcase120b hcase101a hcase420a hcase420b hcase430a hcase430b hcase410a hcase410b hcase340b hcase300b hcase310b hcase00 hcase01 hcase03 hcase13 hcase14 hcase32 hcase40 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase110b hcase120b hcase101a hcase420a hcase420b hcase430a hcase430b hcase410a hcase410b hcase340b hcase300a hcase300b hcase311a hcase00 hcase01 hcase03 hcase13 hcase14 hcase32 hcase40 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase110b hcase120b hcase101a hcase420a hcase420b hcase430a hcase430b hcase410a hcase410b hcase340b hcase301a hcase00 hcase01 hcase03 hcase13 hcase14 hcase31 hcase32 hcase40 hcase44
                        omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130a hcase130b hcase040b hcase020b hcase110a hcase110b hcase120a hcase120b hcase101a hcase101b hcase420b hcase430b hcase410b hcase341a hcase341b hcase400b hcase010b hcase00 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase020a hcase020b hcase110b hcase120b hcase101a hcase420b hcase430b hcase410b hcase400b hcase011a hcase00 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase44
                          omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase110a hcase110b hcase120a hcase120b hcase101a hcase101b hcase420a hcase420b hcase430b hcase410b hcase401a hcase440b hcase00 hcase01 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32
                          omega
                        ·
                          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                          ·
                            clear hn4 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase020a hcase020b hcase110b hcase120b hcase101a hcase420a hcase420b hcase430b hcase410b hcase401a hcase441a hcase010b hcase00 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32
                            omega
                          ·
                            clear hn4 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase020a hcase020b hcase110b hcase120b hcase101a hcase420a hcase420b hcase430a hcase430b hcase410b hcase401a hcase441a hcase011a hcase00 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32
                            omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase110a hcase110b hcase120a hcase120b hcase101a hcase420a hcase420b hcase430a hcase430b hcase00 hcase01 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase44
                    omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase331a hcase331b hcase110a hcase110b hcase120a hcase120b hcase101a hcase101b hcase420b hcase431a hcase400b hcase410b hcase00 hcase01 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase110a hcase110b hcase120a hcase120b hcase101a hcase420a hcase420b hcase431a hcase400b hcase411a hcase00 hcase01 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                      omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase331a hcase331b hcase110a hcase110b hcase120a hcase120b hcase101a hcase101b hcase420b hcase431a hcase401a hcase440b hcase00 hcase01 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase331a hcase331b hcase110a hcase110b hcase120a hcase120b hcase101a hcase101b hcase420b hcase431a hcase401a hcase441a hcase00 hcase01 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41
                      omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase110a hcase110b hcase120a hcase120b hcase101a hcase00 hcase01 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase43 hcase44
                omega
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase331b hcase110a hcase110b hcase121a hcase100b hcase140b hcase00 hcase01 hcase03 hcase13 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase331a hcase331b hcase110b hcase121a hcase100b hcase141a hcase00 hcase01 hcase03 hcase13 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase331a hcase331b hcase110a hcase110b hcase101a hcase101b hcase320b hcase00 hcase01 hcase03 hcase13 hcase14 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase110a hcase110b hcase121a hcase101a hcase321a hcase00 hcase01 hcase03 hcase13 hcase14 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase020a hcase020b hcase331a hcase331b hcase140a hcase140b hcase320b hcase00 hcase01 hcase03 hcase10 hcase12 hcase13 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase331b hcase111a hcase140b hcase321a hcase321b hcase100b hcase00 hcase01 hcase03 hcase12 hcase13 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase111a hcase140a hcase140b hcase321a hcase101a hcase00 hcase01 hcase03 hcase12 hcase13 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase331a hcase331b hcase111a hcase141a hcase100b hcase120b hcase00 hcase01 hcase03 hcase13 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase111a hcase141a hcase100a hcase100b hcase121a hcase00 hcase01 hcase03 hcase13 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase020a hcase020b hcase111a hcase141a hcase101a hcase00 hcase01 hcase03 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
    ·
      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
      ·
        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase100b hcase120b hcase00 hcase01 hcase03 hcase11 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase100b hcase121a hcase140b hcase00 hcase01 hcase03 hcase11 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase021a hcase021b hcase100b hcase121a hcase141a hcase110b hcase00 hcase01 hcase03 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase100a hcase100b hcase121a hcase141a hcase111a hcase00 hcase01 hcase03 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
      ·
        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
        ·
          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase101a hcase101b hcase120a hcase120b hcase340b hcase00 hcase01 hcase03 hcase11 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut36 hcut21 hcut35 hcut30 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase101a hcase101b hcase120a hcase120b hcase341a hcase110a hcase110b hcase430b hcase010a hcase010b hcase410b hcase420a hcase420b hcase440b hcase00 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40
                        omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase021a hcase021b hcase101a hcase101b hcase120a hcase120b hcase341a hcase341b hcase110a hcase110b hcase430a hcase430b hcase010a hcase010b hcase410b hcase420b hcase441a hcase400b hcase00 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase040b hcase101a hcase120b hcase341a hcase110b hcase430b hcase010b hcase410b hcase420b hcase441a hcase401a hcase00 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase101a hcase120a hcase120b hcase341a hcase341b hcase110a hcase110b hcase430a hcase430b hcase010a hcase010b hcase410a hcase410b hcase00 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase101a hcase120a hcase120b hcase341a hcase341b hcase110a hcase110b hcase430a hcase430b hcase010a hcase010b hcase00 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase42 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase101a hcase120b hcase341a hcase341b hcase110b hcase430a hcase430b hcase00 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase101a hcase120b hcase341a hcase341b hcase110b hcase00 hcase01 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase44
                omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase021a hcase021b hcase101a hcase101b hcase120a hcase120b hcase341a hcase341b hcase320b hcase00 hcase01 hcase03 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase101a hcase120a hcase120b hcase341a hcase341b hcase111a hcase321a hcase00 hcase01 hcase03 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase040a hcase040b hcase021a hcase021b hcase101a hcase101b hcase320b hcase00 hcase01 hcase03 hcase11 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase040a hcase040b hcase101a hcase121a hcase321a hcase00 hcase01 hcase03 hcase11 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
  ·
    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
    ·
      rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
      ·
        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase100b hcase120b hcase140b hcase00 hcase01 hcase02 hcase03 hcase11 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase100b hcase120b hcase141a hcase00 hcase01 hcase02 hcase03 hcase11 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase100a hcase100b hcase121a hcase121b hcase140b hcase00 hcase01 hcase02 hcase03 hcase11 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase100b hcase121a hcase141a hcase110b hcase00 hcase01 hcase02 hcase03 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase100b hcase121a hcase141a hcase111a hcase00 hcase01 hcase02 hcase03 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
    ·
      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
      ·
        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
        ·
          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase101a hcase101b hcase320b hcase110a hcase110b hcase340b hcase300b hcase310b hcase00 hcase01 hcase02 hcase03 hcase12 hcase13 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase101a hcase101b hcase320a hcase320b hcase110a hcase110b hcase340a hcase340b hcase300a hcase300b hcase311a hcase311b hcase140b hcase00 hcase01 hcase02 hcase03 hcase12 hcase13 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase320a hcase320b hcase110a hcase110b hcase340b hcase300b hcase311a hcase00 hcase01 hcase02 hcase03 hcase12 hcase13 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase101a hcase101b hcase320b hcase110a hcase110b hcase340b hcase301a hcase330b hcase00 hcase01 hcase02 hcase03 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320b hcase110a hcase110b hcase340b hcase301a hcase331a hcase00 hcase01 hcase02 hcase03 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase101a hcase101b hcase320a hcase320b hcase110a hcase110b hcase341a hcase341b hcase140b hcase00 hcase01 hcase02 hcase03 hcase12 hcase13 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320b hcase110a hcase110b hcase341a hcase141a hcase141b hcase120a hcase120b hcase330b hcase310b hcase00 hcase01 hcase02 hcase03 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                              ·
                                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                                ·
                                  clear hn4 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130a hcase130b hcase041a hcase101a hcase101b hcase320a hcase320b hcase110a hcase110b hcase341a hcase341b hcase141a hcase141b hcase120a hcase120b hcase330a hcase330b hcase300a hcase300b hcase400b hcase410b hcase420b hcase430b hcase010b hcase020b hcase00 hcase03 hcase13 hcase44
                                  omega
                                ·
                                  clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130a hcase130b hcase041a hcase101a hcase320a hcase320b hcase110a hcase110b hcase341a hcase341b hcase141a hcase120a hcase120b hcase330a hcase330b hcase300a hcase300b hcase400b hcase410b hcase420b hcase430b hcase010b hcase021a hcase00 hcase03 hcase13 hcase44
                                  omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320a hcase320b hcase110a hcase110b hcase341a hcase341b hcase141a hcase141b hcase120a hcase120b hcase330b hcase311a hcase311b hcase300a hcase300b hcase400a hcase400b hcase410a hcase410b hcase420a hcase420b hcase430a hcase430b hcase00 hcase02 hcase03 hcase13 hcase44
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320a hcase320b hcase110a hcase110b hcase341a hcase341b hcase141a hcase141b hcase120a hcase120b hcase330a hcase330b hcase311a hcase311b hcase300a hcase300b hcase400b hcase410b hcase420b hcase431a hcase00 hcase01 hcase02 hcase03 hcase13 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320b hcase110a hcase110b hcase341a hcase341b hcase141a hcase141b hcase120a hcase120b hcase330a hcase330b hcase311a hcase311b hcase300a hcase300b hcase400a hcase400b hcase410a hcase410b hcase00 hcase01 hcase02 hcase03 hcase13 hcase43 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320b hcase110a hcase110b hcase341a hcase341b hcase141a hcase141b hcase120a hcase120b hcase330a hcase330b hcase311a hcase311b hcase300a hcase300b hcase400a hcase400b hcase00 hcase01 hcase02 hcase03 hcase13 hcase42 hcase43 hcase44
                          omega
                      ·
                        rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320b hcase110a hcase110b hcase341a hcase141b hcase120a hcase120b hcase330b hcase311a hcase300b hcase401a hcase010a hcase010b hcase440b hcase00 hcase02 hcase03 hcase13 hcase41 hcase42 hcase43
                            omega
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                              ·
                                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                                ·
                                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                                  ·
                                    clear hn4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130a hcase130b hcase041a hcase101a hcase101b hcase320b hcase110a hcase110b hcase341a hcase141a hcase141b hcase120a hcase120b hcase330b hcase311a hcase300b hcase401a hcase010b hcase441a hcase410b hcase420b hcase430b hcase020b hcase00 hcase03 hcase13
                                    omega
                                  ·
                                    clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130a hcase130b hcase041a hcase101a hcase320a hcase320b hcase110a hcase110b hcase341a hcase141a hcase120a hcase120b hcase330a hcase330b hcase311a hcase300b hcase401a hcase010b hcase441a hcase410b hcase420b hcase430b hcase021a hcase00 hcase03 hcase13
                                    omega
                                ·
                                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320a hcase320b hcase110a hcase110b hcase341a hcase341b hcase141a hcase141b hcase120a hcase120b hcase330a hcase330b hcase311a hcase311b hcase300a hcase300b hcase401a hcase010a hcase010b hcase441a hcase410a hcase410b hcase420b hcase431a hcase00 hcase02 hcase03 hcase13
                                  omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320b hcase110a hcase110b hcase341a hcase341b hcase141a hcase141b hcase120a hcase120b hcase330a hcase330b hcase311a hcase311b hcase300a hcase300b hcase401a hcase401b hcase010a hcase010b hcase441a hcase441b hcase410a hcase410b hcase00 hcase02 hcase03 hcase13 hcase43
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320b hcase110a hcase110b hcase341a hcase341b hcase141a hcase141b hcase120a hcase120b hcase330a hcase330b hcase311a hcase311b hcase300a hcase300b hcase401a hcase401b hcase010a hcase010b hcase441a hcase441b hcase00 hcase02 hcase03 hcase13 hcase42 hcase43
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320a hcase320b hcase110a hcase110b hcase341a hcase341b hcase141a hcase141b hcase120a hcase120b hcase330b hcase311a hcase311b hcase300a hcase300b hcase401a hcase401b hcase011a hcase00 hcase02 hcase03 hcase13 hcase41 hcase42 hcase43 hcase44
                          omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320b hcase110a hcase110b hcase341a hcase141b hcase120a hcase120b hcase330a hcase330b hcase311a hcase301a hcase410b hcase430b hcase440b hcase00 hcase01 hcase02 hcase03 hcase13 hcase40 hcase42
                            omega
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130a hcase130b hcase041a hcase101a hcase320b hcase110a hcase110b hcase341a hcase141a hcase120a hcase120b hcase330a hcase330b hcase311a hcase410a hcase410b hcase430b hcase441a hcase400b hcase00 hcase01 hcase02 hcase03 hcase13 hcase42
                              omega
                            ·
                              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                              ·
                                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                                ·
                                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                                  ·
                                    clear hn4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130a hcase130b hcase041a hcase101a hcase101b hcase320b hcase110a hcase110b hcase341a hcase141a hcase141b hcase120a hcase120b hcase330b hcase311a hcase301a hcase410b hcase430b hcase441a hcase401a hcase010b hcase020b hcase420b hcase00 hcase03 hcase13
                                    omega
                                  ·
                                    clear hn4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut31 hcut48 hcut58 hcut15 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130a hcase130b hcase041a hcase101a hcase101b hcase320b hcase110a hcase110b hcase341a hcase141a hcase141b hcase120a hcase120b hcase330a hcase330b hcase311a hcase301a hcase410b hcase430b hcase441a hcase401a hcase010b hcase020b hcase421a hcase00 hcase03 hcase13
                                    omega
                                ·
                                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase320a hcase320b hcase110b hcase341a hcase341b hcase141a hcase120b hcase330a hcase330b hcase311a hcase311b hcase301a hcase301b hcase410a hcase410b hcase430a hcase430b hcase441a hcase441b hcase401a hcase401b hcase010a hcase010b hcase00 hcase03 hcase13 hcase42
                                  omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320a hcase320b hcase110a hcase110b hcase341a hcase341b hcase141a hcase141b hcase120a hcase120b hcase330b hcase311a hcase311b hcase301a hcase301b hcase410a hcase410b hcase430a hcase430b hcase441a hcase441b hcase401a hcase401b hcase00 hcase02 hcase03 hcase13 hcase42
                                omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320a hcase320b hcase110a hcase110b hcase341a hcase341b hcase141a hcase141b hcase120a hcase120b hcase330b hcase311a hcase311b hcase301a hcase301b hcase410a hcase410b hcase00 hcase01 hcase02 hcase03 hcase13 hcase40 hcase42 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320b hcase110a hcase110b hcase341a hcase341b hcase141a hcase141b hcase120a hcase120b hcase330a hcase330b hcase311a hcase311b hcase301a hcase301b hcase00 hcase01 hcase02 hcase03 hcase13 hcase40 hcase42 hcase43 hcase44
                        omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase320a hcase320b hcase110b hcase341a hcase341b hcase141a hcase120b hcase00 hcase01 hcase02 hcase03 hcase13 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320b hcase110a hcase110b hcase341a hcase341b hcase141a hcase141b hcase00 hcase01 hcase02 hcase03 hcase13 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase101b hcase320b hcase00 hcase01 hcase02 hcase03 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase101a hcase101b hcase321a hcase321b hcase140b hcase00 hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
          ·
            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase141a hcase430a hcase430b hcase440a hcase440b hcase110b hcase120b hcase00 hcase01 hcase02 hcase03 hcase13 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42
                  omega
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase321a hcase430a hcase430b hcase440a hcase440b hcase110a hcase110b hcase121a hcase121b hcase310b hcase340b hcase300b hcase00 hcase01 hcase02 hcase03 hcase13 hcase33 hcase40 hcase41 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase321a hcase430a hcase430b hcase440a hcase440b hcase110a hcase110b hcase121a hcase121b hcase310a hcase310b hcase340b hcase301a hcase00 hcase01 hcase02 hcase03 hcase13 hcase33 hcase40 hcase41 hcase42
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase141a hcase430b hcase440b hcase110a hcase110b hcase121a hcase310a hcase310b hcase00 hcase01 hcase02 hcase03 hcase13 hcase30 hcase33 hcase40 hcase41 hcase42
                      omega
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      clear hn4 hsum_nat0 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase430b hcase440b hcase110a hcase110b hcase121a hcase311a hcase300b hcase00 hcase01 hcase02 hcase03 hcase13 hcase33 hcase34 hcase40 hcase41 hcase42
                      omega
                    ·
                      clear hn4 hsum_nat0 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase430b hcase440b hcase110a hcase110b hcase121a hcase311a hcase301a hcase00 hcase01 hcase02 hcase03 hcase13 hcase33 hcase34 hcase40 hcase41 hcase42
                      omega
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut46 hcut52 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase430a hcase430b hcase440a hcase440b hcase111a hcase310b hcase120b hcase340b hcase300b hcase00 hcase01 hcase02 hcase03 hcase13 hcase33 hcase40 hcase41 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase321a hcase430a hcase430b hcase440a hcase440b hcase111a hcase111b hcase310a hcase310b hcase120a hcase120b hcase340b hcase301a hcase00 hcase01 hcase02 hcase03 hcase13 hcase33 hcase40 hcase41 hcase42
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase141a hcase430b hcase440b hcase111a hcase310a hcase310b hcase120a hcase120b hcase00 hcase01 hcase02 hcase03 hcase13 hcase30 hcase33 hcase40 hcase41 hcase42
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase141a hcase430a hcase430b hcase440a hcase440b hcase111a hcase310a hcase310b hcase121a hcase00 hcase01 hcase02 hcase03 hcase13 hcase30 hcase33 hcase34 hcase40 hcase41 hcase42
                    omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hn4 hsum_nat0 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase430b hcase440b hcase111a hcase311a hcase300b hcase00 hcase01 hcase02 hcase03 hcase12 hcase13 hcase33 hcase34 hcase40 hcase41 hcase42
                    omega
                  ·
                    clear hn4 hsum_nat0 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase430b hcase440b hcase111a hcase311a hcase301a hcase00 hcase01 hcase02 hcase03 hcase12 hcase13 hcase33 hcase34 hcase40 hcase41 hcase42
                    omega
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase321a hcase430a hcase430b hcase441a hcase441b hcase340b hcase300b hcase00 hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase31 hcase33 hcase40 hcase41 hcase42
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130a hcase130b hcase041a hcase041b hcase101a hcase321a hcase430a hcase430b hcase441a hcase441b hcase340b hcase301a hcase00 hcase01 hcase02 hcase03 hcase11 hcase12 hcase13 hcase31 hcase33 hcase40 hcase41 hcase42
                  omega
              ·
                rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase141a hcase430a hcase430b hcase441a hcase441b hcase341a hcase341b hcase120b hcase310a hcase310b hcase300a hcase300b hcase010a hcase010b hcase110b hcase00 hcase02 hcase03 hcase13 hcase33 hcase40 hcase41 hcase42
                          omega
                        ·
                          clear hn4 hcut55 hcut46 hcut52 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase041a hcase101a hcase321a hcase141a hcase430b hcase441a hcase341a hcase120b hcase310b hcase300b hcase010b hcase111a hcase00 hcase02 hcase03 hcase13 hcase33 hcase40 hcase41 hcase42
                          omega
                      ·
                        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase141a hcase430a hcase430b hcase441a hcase441b hcase341a hcase120b hcase310b hcase300a hcase300b hcase110b hcase00 hcase02 hcase03 hcase13 hcase33 hcase40 hcase41 hcase42
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase141a hcase430a hcase430b hcase441a hcase441b hcase341a hcase341b hcase120a hcase120b hcase310a hcase310b hcase300a hcase300b hcase111a hcase00 hcase02 hcase03 hcase13 hcase33 hcase40 hcase41 hcase42
                          omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase141a hcase430a hcase430b hcase441a hcase441b hcase341a hcase341b hcase120b hcase310a hcase310b hcase301a hcase301b hcase110b hcase00 hcase01 hcase02 hcase03 hcase13 hcase33 hcase40 hcase41 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase141a hcase430a hcase430b hcase441a hcase441b hcase341a hcase120a hcase120b hcase310b hcase301a hcase111a hcase00 hcase01 hcase02 hcase03 hcase13 hcase33 hcase40 hcase41 hcase42
                        omega
                  ·
                    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase041a hcase101a hcase141a hcase430b hcase441a hcase341a hcase341b hcase120a hcase120b hcase010b hcase400b hcase00 hcase02 hcase03 hcase11 hcase13 hcase30 hcase33 hcase41 hcase42
                        omega
                      ·
                        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase141a hcase430a hcase430b hcase441a hcase441b hcase341a hcase341b hcase120b hcase311a hcase311b hcase010a hcase010b hcase401a hcase401b hcase110b hcase00 hcase02 hcase03 hcase13 hcase30 hcase33 hcase41 hcase42
                          omega
                        ·
                          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                          ·
                            clear hn4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase041a hcase101a hcase321a hcase141a hcase430b hcase441a hcase341a hcase120a hcase120b hcase311a hcase010b hcase401a hcase111a hcase300b hcase00 hcase02 hcase03 hcase13 hcase33 hcase41 hcase42
                            omega
                          ·
                            clear hn4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase041a hcase101a hcase321a hcase141a hcase430b hcase441a hcase341a hcase120a hcase120b hcase311a hcase010b hcase401a hcase111a hcase301a hcase00 hcase02 hcase03 hcase13 hcase33 hcase41 hcase42
                            omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase141a hcase430a hcase430b hcase441a hcase441b hcase341a hcase341b hcase120b hcase311a hcase311b hcase110b hcase00 hcase02 hcase03 hcase13 hcase30 hcase33 hcase40 hcase41 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase141a hcase430a hcase430b hcase441a hcase441b hcase341a hcase341b hcase120a hcase120b hcase311a hcase311b hcase111a hcase00 hcase02 hcase03 hcase13 hcase30 hcase33 hcase40 hcase41 hcase42
                        omega
                ·
                  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130a hcase130b hcase041a hcase321a hcase141a hcase430b hcase441a hcase341a hcase341b hcase010b hcase300a hcase300b hcase400b hcase00 hcase02 hcase03 hcase11 hcase13 hcase31 hcase33 hcase41 hcase42
                        omega
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase041a hcase321a hcase141a hcase430b hcase441a hcase341a hcase121a hcase010b hcase300b hcase401a hcase310b hcase00 hcase02 hcase03 hcase11 hcase13 hcase33 hcase41 hcase42
                          omega
                        ·
                          clear hn4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase041a hcase101a hcase321a hcase141a hcase430b hcase441a hcase341a hcase121a hcase010b hcase300b hcase401a hcase311a hcase00 hcase02 hcase03 hcase11 hcase13 hcase33 hcase41 hcase42
                          omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130a hcase130b hcase041a hcase321a hcase141a hcase430b hcase441a hcase341a hcase341b hcase010b hcase301a hcase301b hcase400b hcase00 hcase02 hcase03 hcase11 hcase13 hcase31 hcase33 hcase41 hcase42
                        omega
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase141a hcase430a hcase430b hcase441a hcase441b hcase341a hcase121a hcase010a hcase010b hcase301a hcase401a hcase401b hcase310b hcase00 hcase02 hcase03 hcase11 hcase13 hcase33 hcase41 hcase42
                          omega
                        ·
                          clear hn4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase130b hcase041a hcase101a hcase321a hcase141a hcase430b hcase441a hcase341a hcase121a hcase010b hcase301a hcase401a hcase311a hcase00 hcase02 hcase03 hcase11 hcase13 hcase33 hcase41 hcase42
                          omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase141a hcase430a hcase430b hcase441a hcase441b hcase341a hcase341b hcase121a hcase00 hcase02 hcase03 hcase11 hcase13 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42
                    omega
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase141a hcase110b hcase120b hcase00 hcase01 hcase02 hcase03 hcase13 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase141a hcase110a hcase110b hcase121a hcase00 hcase01 hcase02 hcase03 hcase13 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase130b hcase041a hcase041b hcase101a hcase321a hcase141a hcase111a hcase00 hcase01 hcase02 hcase03 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
              omega

#print axioms symbolic_mask127_integer_shard001
end Jsp404.SixExactFloorKernel
