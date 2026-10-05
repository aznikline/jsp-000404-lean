import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_mask64_integer_shard006 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut11 : (s40 + s42 + s43 + u40 + u42 + u43) + 1 ≤ (n))
    (hcut85 : (s00 + s11 + s33 + u00 + u11 + u33) + 1 ≤ (n + 1))
    (hcut74 : (s00 + s04 + s33 + s40 + u00 + u04 + u33 + u40) + 1 ≤ (2 * n + 1))
    (hcut4 : (s02 + s10 + s14 + s40 + s41 + u02 + u10 + u14 + u40 + u41) + 1 ≤ (n + s30 + 3))
    (hcut23 : (s12 + s13 + s14 + u12 + u13 + u14) + 1 ≤ (n))
    (hcut86 : (s03 + s04 + s30 + u03 + u04 + u30) + 1 ≤ (n + 1))
    (hcut44 : (s31 + u31 + 2) + 1 ≤ (n))
    (hcut50 : (s12 + u12) + 1 ≤ (s33 + 1))
    (hcut37 : (s02 + s03 + s04 + u02 + u03 + u04) + 1 ≤ (n))
    (hcut0 : (s12 + s13 + s42 + s43 + u12 + u13 + u42 + u43) + 1 ≤ (s33 + 2))
    (hcut22 : (s12 + s44 + u12 + u44 + 1) + 1 ≤ (n))
    (hcut60 : (s00 + s31 + s43 + u00 + u31 + u43 + 1) + 1 ≤ (n))
    (hcut65 : (s02 + s03 + s10 + u02 + u03 + u10) + 1 ≤ (n + 1))
    (hcut75 : (s10 + s12 + s13 + u10 + u12 + u13) + 1 ≤ (n))
    (hcut72 : (s40 + s41 + u40 + u41) + 1 ≤ (n))
    (hcut57 : (s13 + s31 + u13 + u31 + 1) + 1 ≤ (n))
    (hcut55 : (s11 + s33 + u11 + u33) + 1 ≤ (n))
    (hcut62 : (s11 + s34 + u11 + u34) + 1 ≤ (n))
    (hcut70 : (s01 + s02 + s31 + s32 + u01 + u02 + u31 + u32) + 1 ≤ (s11 + 2))
    (hcut54 : (s41 + s42 + u41 + u42) + 1 ≤ (n))
    (hcut5 : (s03 + s30 + s34 + s41 + s42 + s43 + u03 + u30 + u34 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut40 : (s31 + s44 + u31 + u44 + 1) + 1 ≤ (n))
    (hcut36 : (s00 + s02 + s04 + s40 + s44 + u00 + u02 + u04 + u40 + u44) + 1 ≤ (2 * n))
    (hcut26 : (s00 + s33 + s44 + u00 + u33 + u44) + 1 ≤ (n + 1))
    (hcut45 : (s00 + u00 + 2) + 1 ≤ (n))
    (hcut30 : (s10 + s13 + s14 + u10 + u13 + u14 + 1) + 1 ≤ (n))
    (hcut1 : (s00 + s11 + s33 + s34 + u00 + u11 + u33 + u34) + 1 ≤ (n + 2))
    (hcut61 : (s10 + s14 + s41 + u10 + u14 + u41) + 1 ≤ (n + 1))
    (hcut71 : (s00 + s04 + s11 + s40 + s44 + u00 + u04 + u11 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut31 : (s03 + s14 + s30 + u03 + u14 + u30) + 1 ≤ (n + 1))
    (hcut18 : (s43 + s44 + u43 + u44 + 2) + 1 ≤ (n))
    (hcut68 : (s34 + s40 + s41 + u34 + u40 + u41) + 1 ≤ (n + 1))
    (hcut64 : (s00 + s11 + u00 + u11) + 1 ≤ (n))
    (hcut3 : (s04 + s40 + u04 + u40) + 1 ≤ (n + 2))
    (hcut77 : (s13 + s14 + s31 + u13 + u14 + u31) + 1 ≤ (n))
    (hcut63 : (s01 + s32 + u01 + u32) + 1 ≤ (s11 + 1))
    (hcut17 : (s42 + s44 + u42 + u44 + 1) + 1 ≤ (n))
    (hcut76 : (s10 + s13 + s31 + u10 + u13 + u31) + 1 ≤ (n))
    (hcut51 : (s13 + u13 + 2) + 1 ≤ (n))
    (hcut24 : (s11 + s33 + s44 + u11 + u33 + u44) + 1 ≤ (n + 1))
    (hcut16 : (s40 + s41 + s42 + s43 + s44 + u40 + u41 + u42 + u43 + u44) + 1 ≤ (n + 1))
    (hcut73 : (s00 + s12 + u00 + u12 + 1) + 1 ≤ (n))
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
    (hcase020a : s02 = 0)
    (hcase020b : u02 = 0)
    (hcase031a : 1 ≤ s03)
    (hcase031b : u03 = 1)
    (hcase001a : 1 ≤ s00)
    (hcase001b : u00 = 1)
    : False := by
  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
  ·
    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
    ·
      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
      ·
        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120b hcase140b hcase300a hcase300b hcase110b hcase100b hcase130b hcase00 hcase01 hcase02 hcase03 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120b hcase140b hcase300a hcase300b hcase110b hcase100b hcase131a hcase00 hcase01 hcase02 hcase03 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120b hcase140b hcase300a hcase300b hcase110b hcase101a hcase130b hcase00 hcase01 hcase02 hcase03 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120b hcase140a hcase140b hcase300a hcase300b hcase110b hcase101a hcase131a hcase00 hcase01 hcase02 hcase03 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase300b hcase111a hcase111b hcase010a hcase010b hcase330b hcase320b hcase310b hcase340b hcase00 hcase02 hcase03 hcase10 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase300b hcase010a hcase010b hcase330b hcase320b hcase310b hcase341a hcase00 hcase02 hcase03 hcase10 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase300b hcase111a hcase111b hcase010a hcase010b hcase330b hcase320b hcase311a hcase340b hcase00 hcase02 hcase03 hcase10 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase140a hcase140b hcase300a hcase300b hcase111a hcase111b hcase010b hcase330b hcase320b hcase311a hcase341a hcase00 hcase02 hcase03 hcase10 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase300b hcase111a hcase010a hcase010b hcase330b hcase321a hcase340b hcase00 hcase02 hcase03 hcase10 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase300b hcase111a hcase010a hcase010b hcase330b hcase321a hcase341a hcase310b hcase00 hcase02 hcase03 hcase10 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase300b hcase111a hcase010a hcase010b hcase330b hcase321a hcase341a hcase311a hcase00 hcase02 hcase03 hcase10 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase300b hcase010a hcase010b hcase331a hcase310b hcase320b hcase00 hcase02 hcase03 hcase10 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase300b hcase111a hcase010a hcase010b hcase331a hcase310b hcase321a hcase00 hcase02 hcase03 hcase10 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120b hcase140b hcase300a hcase300b hcase111a hcase010a hcase010b hcase311a hcase311b hcase320a hcase320b hcase100b hcase130b hcase00 hcase02 hcase03 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120a hcase120b hcase140b hcase300a hcase300b hcase111a hcase010a hcase010b hcase331a hcase311a hcase311b hcase320a hcase320b hcase100b hcase131a hcase00 hcase02 hcase03 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                      ·
                        clear hn4 hsum_nat3 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120b hcase140b hcase300a hcase300b hcase111a hcase010b hcase311a hcase311b hcase320a hcase320b hcase101a hcase130b hcase00 hcase02 hcase03 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120b hcase140b hcase300b hcase111a hcase010a hcase010b hcase331a hcase311a hcase320b hcase101a hcase131a hcase00 hcase02 hcase03 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase300b hcase111a hcase010a hcase010b hcase331a hcase311a hcase321a hcase00 hcase02 hcase03 hcase10 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase300b hcase111a hcase310b hcase00 hcase02 hcase03 hcase10 hcase13 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase300b hcase111a hcase311a hcase00 hcase02 hcase03 hcase10 hcase13 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase320b hcase330b hcase010b hcase310b hcase00 hcase02 hcase03 hcase10 hcase11 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase320b hcase330b hcase010b hcase311a hcase00 hcase02 hcase03 hcase10 hcase11 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase301b hcase320a hcase320b hcase330a hcase330b hcase110b hcase00 hcase02 hcase03 hcase10 hcase13 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase320a hcase320b hcase330b hcase011a hcase111a hcase310b hcase00 hcase02 hcase03 hcase10 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase320a hcase320b hcase330b hcase011a hcase111a hcase311a hcase00 hcase02 hcase03 hcase10 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                      ·
                        clear hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120b hcase140b hcase301a hcase301b hcase320a hcase320b hcase331a hcase331b hcase310a hcase310b hcase010a hcase010b hcase110b hcase100b hcase130b hcase00 hcase02 hcase03 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120a hcase120b hcase140b hcase301b hcase320a hcase320b hcase331a hcase331b hcase310a hcase310b hcase010a hcase010b hcase110b hcase100b hcase131a hcase00 hcase02 hcase03 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                      ·
                        clear hn4 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120b hcase140b hcase301a hcase301b hcase320a hcase320b hcase331a hcase331b hcase310a hcase310b hcase010b hcase110b hcase101a hcase130b hcase00 hcase02 hcase03 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120b hcase140a hcase140b hcase301a hcase301b hcase320a hcase320b hcase331a hcase331b hcase310a hcase310b hcase010a hcase010b hcase110b hcase101a hcase131a hcase00 hcase02 hcase03 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase320b hcase331a hcase310b hcase010b hcase00 hcase02 hcase03 hcase10 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase301b hcase320a hcase320b hcase331a hcase331b hcase310a hcase310b hcase110b hcase00 hcase02 hcase03 hcase10 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase320a hcase320b hcase331a hcase310b hcase011a hcase111a hcase00 hcase02 hcase03 hcase10 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase301b hcase320a hcase320b hcase331a hcase331b hcase110b hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120b hcase140b hcase301a hcase301b hcase320a hcase320b hcase311a hcase311b hcase111a hcase130b hcase100b hcase00 hcase01 hcase02 hcase03 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        clear hn4 hsum_nat3 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120b hcase140b hcase301a hcase301b hcase320a hcase320b hcase311a hcase311b hcase111a hcase130b hcase101a hcase010b hcase00 hcase02 hcase03 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase320a hcase320b hcase331a hcase311a hcase111a hcase130a hcase130b hcase101a hcase101b hcase011a hcase00 hcase02 hcase03 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120a hcase120b hcase140b hcase301a hcase301b hcase320a hcase320b hcase331a hcase311a hcase311b hcase111a hcase131a hcase100b hcase00 hcase01 hcase02 hcase03 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        clear hn4 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120b hcase140b hcase301a hcase320b hcase331a hcase311a hcase111a hcase131a hcase101a hcase010b hcase00 hcase02 hcase03 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase320a hcase320b hcase331a hcase311a hcase111a hcase131a hcase131b hcase101a hcase101b hcase011a hcase00 hcase02 hcase03 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase301b hcase110b hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase321a hcase111a hcase310b hcase330b hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase321a hcase111a hcase310b hcase331a hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase321a hcase111a hcase311a hcase330b hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase140a hcase140b hcase301a hcase321a hcase111a hcase311a hcase331a hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
      ·
        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
        ·
          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase330b hcase340b hcase310b hcase110b hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase330b hcase340b hcase310b hcase111a hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase330b hcase340b hcase110b hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase330b hcase340b hcase311a hcase111a hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase141a hcase141b hcase330b hcase341a hcase320b hcase010b hcase310b hcase00 hcase02 hcase03 hcase10 hcase11 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase141a hcase141b hcase330b hcase341a hcase320b hcase010b hcase311a hcase00 hcase02 hcase03 hcase10 hcase11 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120a hcase120b hcase141a hcase141b hcase330a hcase330b hcase341a hcase341b hcase320a hcase320b hcase110b hcase00 hcase02 hcase03 hcase10 hcase13 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase120a hcase120b hcase141a hcase141b hcase330a hcase330b hcase341a hcase320a hcase320b hcase111a hcase300b hcase00 hcase02 hcase03 hcase10 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase141a hcase141b hcase330a hcase330b hcase320a hcase320b hcase011a hcase111a hcase301a hcase00 hcase02 hcase03 hcase10 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120a hcase120b hcase141a hcase141b hcase330a hcase330b hcase341a hcase341b hcase110b hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase141a hcase141b hcase330a hcase330b hcase321a hcase111a hcase310b hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase141a hcase141b hcase330a hcase330b hcase321a hcase111a hcase311a hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                clear hn4 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120b hcase141a hcase331a hcase331b hcase110b hcase130b hcase100b hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120b hcase141a hcase331a hcase331b hcase110b hcase130a hcase130b hcase101a hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase120b hcase141a hcase331a hcase331b hcase110b hcase131a hcase00 hcase01 hcase02 hcase03 hcase10 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase331a hcase320b hcase310b hcase010b hcase00 hcase02 hcase03 hcase10 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase331a hcase111a hcase320a hcase320b hcase310b hcase011a hcase00 hcase02 hcase03 hcase10 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase331a hcase111a hcase320a hcase320b hcase311a hcase340b hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase331a hcase111a hcase320a hcase320b hcase311a hcase341a hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase331a hcase111a hcase321a hcase310b hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase120a hcase120b hcase331a hcase111a hcase321a hcase311a hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
    ·
      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
      ·
        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase121a hcase010a hcase010b hcase100b hcase110b hcase130b hcase140b hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase121a hcase010b hcase100b hcase110b hcase130b hcase141a hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase121a hcase010a hcase010b hcase100b hcase110b hcase131a hcase140b hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase121a hcase010a hcase010b hcase100b hcase110b hcase131a hcase141a hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase010a hcase010b hcase100a hcase100b hcase111a hcase111b hcase330b hcase00 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase121a hcase010a hcase010b hcase100b hcase111a hcase331a hcase130b hcase140b hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase121a hcase010b hcase100b hcase111a hcase331a hcase130b hcase141a hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase121a hcase010a hcase010b hcase100b hcase111a hcase331a hcase131a hcase140b hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase121a hcase010b hcase100b hcase111a hcase331a hcase131a hcase141a hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase010a hcase010b hcase101a hcase101b hcase140a hcase140b hcase130a hcase130b hcase330b hcase00 hcase02 hcase03 hcase11 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  clear hn4 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase121a hcase010b hcase101a hcase140b hcase130b hcase331a hcase331b hcase110b hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase121a hcase010b hcase101a hcase140b hcase130b hcase331a hcase111a hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase121a hcase010a hcase010b hcase101a hcase140b hcase131a hcase110b hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase010a hcase010b hcase101a hcase101b hcase140a hcase140b hcase111a hcase111b hcase330b hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase121a hcase010b hcase101a hcase140b hcase131a hcase111a hcase331a hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase010a hcase010b hcase101a hcase101b hcase141a hcase141b hcase320a hcase320b hcase330b hcase00 hcase02 hcase03 hcase11 hcase13 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase121b hcase010b hcase101b hcase141b hcase320b hcase331a hcase130a hcase130b hcase310b hcase110a hcase110b hcase340a hcase340b hcase400b hcase00 hcase02 hcase03 hcase30 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              clear hn4 hcut11 hcut85 hcut74 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase121a hcase010b hcase101a hcase320b hcase331a hcase130b hcase310b hcase110b hcase340b hcase401a hcase420b hcase430b hcase00 hcase02 hcase03 hcase30 hcase41 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase121a hcase121b hcase010b hcase101a hcase101b hcase141a hcase141b hcase320b hcase331a hcase130a hcase130b hcase310b hcase110a hcase110b hcase340a hcase340b hcase401a hcase420a hcase420b hcase00 hcase02 hcase03 hcase30 hcase41 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat1 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase121a hcase121b hcase010b hcase101a hcase101b hcase141a hcase141b hcase320b hcase331a hcase130a hcase130b hcase310b hcase110a hcase110b hcase340a hcase340b hcase401a hcase00 hcase02 hcase03 hcase30 hcase41 hcase43 hcase44
                            omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase040a hcase040b hcase121a hcase121b hcase010a hcase010b hcase101a hcase101b hcase141a hcase141b hcase320a hcase320b hcase331a hcase331b hcase130a hcase130b hcase310a hcase310b hcase110a hcase110b hcase440b hcase400b hcase00 hcase02 hcase03 hcase30 hcase41 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat3 hcut11 hcut85 hcut74 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase121a hcase010b hcase101a hcase141a hcase320a hcase320b hcase331a hcase130b hcase310a hcase310b hcase110a hcase110b hcase440b hcase401a hcase00 hcase02 hcase03 hcase30 hcase41 hcase42 hcase43
                            omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase121a hcase121b hcase010b hcase101a hcase101b hcase141a hcase141b hcase320b hcase331a hcase130a hcase130b hcase310b hcase110a hcase110b hcase341a hcase00 hcase02 hcase03 hcase30 hcase40 hcase41 hcase42 hcase43
                          omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase121a hcase121b hcase010b hcase101a hcase101b hcase320b hcase331a hcase130a hcase130b hcase310b hcase00 hcase02 hcase03 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase121a hcase121b hcase010a hcase010b hcase101a hcase101b hcase141a hcase141b hcase320a hcase320b hcase331a hcase331b hcase130a hcase130b hcase340a hcase340b hcase110b hcase00 hcase02 hcase03 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase121a hcase121b hcase010a hcase010b hcase101a hcase101b hcase320a hcase320b hcase331a hcase130a hcase130b hcase311a hcase340b hcase111a hcase00 hcase02 hcase03 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase121a hcase121b hcase010a hcase010b hcase101a hcase101b hcase141a hcase141b hcase320a hcase320b hcase331a hcase331b hcase130a hcase130b hcase341a hcase341b hcase110b hcase00 hcase02 hcase03 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase121a hcase121b hcase010a hcase010b hcase101a hcase101b hcase320a hcase320b hcase331a hcase130a hcase130b hcase311a hcase341a hcase111a hcase00 hcase02 hcase03 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat3 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase121a hcase010b hcase101a hcase141a hcase320a hcase320b hcase331a hcase110a hcase110b hcase440b hcase400b hcase00 hcase02 hcase03 hcase30 hcase31 hcase34 hcase41 hcase42 hcase43
                        omega
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase121a hcase121b hcase010a hcase010b hcase320a hcase320b hcase331a hcase331b hcase131a hcase131b hcase110a hcase110b hcase440b hcase401a hcase420b hcase430b hcase300b hcase00 hcase02 hcase03 hcase31 hcase34 hcase41
                              omega
                            ·
                              clear hn4 hsum_nat3 hcut11 hcut74 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase121a hcase010b hcase101a hcase320a hcase320b hcase331a hcase131a hcase110a hcase110b hcase440b hcase401a hcase420a hcase420b hcase430a hcase430b hcase301a hcase00 hcase02 hcase03 hcase31 hcase34 hcase41
                              omega
                          ·
                            clear hn4 hsum_nat0 hcut11 hcut85 hcut74 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase121a hcase010a hcase010b hcase101a hcase141a hcase320a hcase320b hcase331a hcase331b hcase131a hcase110b hcase440b hcase401a hcase420a hcase420b hcase431a hcase00 hcase02 hcase03 hcase30 hcase31 hcase34 hcase41
                            omega
                        ·
                          clear hn4 hsum_nat0 hcut11 hcut85 hcut74 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase121a hcase010a hcase010b hcase101a hcase141a hcase320a hcase320b hcase331a hcase331b hcase131a hcase110b hcase440b hcase401a hcase421a hcase00 hcase02 hcase03 hcase30 hcase31 hcase34 hcase41 hcase43
                          omega
                    ·
                      clear hn4 hsum_nat3 hcut11 hcut85 hcut74 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase121a hcase010b hcase101a hcase141a hcase320a hcase320b hcase331a hcase131a hcase110b hcase00 hcase02 hcase03 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43
                      omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase121a hcase121b hcase010b hcase101a hcase101b hcase320b hcase331a hcase131a hcase131b hcase310b hcase00 hcase02 hcase03 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase121a hcase121b hcase010a hcase010b hcase101a hcase101b hcase320a hcase320b hcase331a hcase131a hcase131b hcase111a hcase311a hcase340b hcase00 hcase02 hcase03 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase121a hcase010b hcase101a hcase141a hcase320a hcase320b hcase331a hcase131a hcase111a hcase311a hcase00 hcase02 hcase03 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase121a hcase121b hcase010a hcase010b hcase101a hcase101b hcase141a hcase141b hcase110b hcase00 hcase02 hcase03 hcase13 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase010a hcase010b hcase101a hcase101b hcase141a hcase141b hcase321a hcase321b hcase111a hcase111b hcase310a hcase310b hcase330b hcase00 hcase02 hcase03 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase121a hcase121b hcase010a hcase010b hcase101a hcase101b hcase321a hcase111a hcase310b hcase331a hcase00 hcase02 hcase03 hcase13 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase010a hcase010b hcase101a hcase101b hcase141a hcase141b hcase321a hcase321b hcase111a hcase111b hcase311a hcase311b hcase300a hcase300b hcase330b hcase00 hcase02 hcase03 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase121a hcase121b hcase010a hcase010b hcase101a hcase101b hcase141a hcase141b hcase321a hcase111a hcase311a hcase300b hcase331a hcase00 hcase02 hcase03 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase121a hcase121b hcase010a hcase010b hcase101a hcase101b hcase321a hcase111a hcase311a hcase301a hcase00 hcase02 hcase03 hcase13 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
      ·
        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase121a hcase121b hcase110b hcase00 hcase02 hcase03 hcase10 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase121a hcase121b hcase111a hcase310b hcase300b hcase00 hcase02 hcase03 hcase10 hcase13 hcase14 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase011a hcase011b hcase111a hcase111b hcase310a hcase310b hcase301a hcase301b hcase330b hcase00 hcase02 hcase03 hcase10 hcase13 hcase14 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase040b hcase121a hcase121b hcase011a hcase111a hcase310b hcase301a hcase331a hcase00 hcase02 hcase03 hcase10 hcase13 hcase14 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase121a hcase121b hcase111a hcase311a hcase300b hcase00 hcase02 hcase03 hcase10 hcase13 hcase14 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase040a hcase040b hcase011a hcase011b hcase111a hcase111b hcase311a hcase311b hcase301a hcase301b hcase330b hcase00 hcase02 hcase03 hcase10 hcase13 hcase14 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase040b hcase121a hcase121b hcase011a hcase111a hcase311a hcase301a hcase331a hcase00 hcase02 hcase03 hcase10 hcase13 hcase14 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
  ·
    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
    ·
      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
      ·
        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              clear hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100b hcase120b hcase130b hcase140b hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001b hcase041b hcase110b hcase100b hcase120b hcase130b hcase141a hcase400a hcase400b hcase340b hcase310b hcase330b hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          clear hn4 hsum_nat0 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase100b hcase120b hcase130b hcase141a hcase400b hcase340b hcase310a hcase310b hcase331a hcase410b hcase420b hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase400b hcase340a hcase340b hcase310a hcase310b hcase331a hcase410b hcase421a hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase400b hcase340a hcase340b hcase310b hcase331a hcase411a hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase42 hcase43 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase400a hcase400b hcase340a hcase340b hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase33 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase400b hcase341a hcase330b hcase310b hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase400b hcase341a hcase330b hcase311a hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase400b hcase341a hcase331a hcase310b hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase400b hcase341a hcase331a hcase311a hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase41 hcase42 hcase43 hcase44
                      omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase100b hcase120b hcase130b hcase141a hcase401a hcase401b hcase430a hcase430b hcase420a hcase420b hcase410a hcase410b hcase440a hcase440b hcase340b hcase330b hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32
                            omega
                          ·
                            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                            ·
                              clear hn4 hsum_nat0 hcut11 hcut85 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase110b hcase100b hcase120b hcase130b hcase141a hcase401a hcase430b hcase420b hcase410b hcase440b hcase340b hcase331a hcase310b hcase00 hcase01 hcase02 hcase03 hcase30 hcase32
                              omega
                            ·
                              clear hn4 hcut11 hcut85 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase110b hcase100b hcase120b hcase130b hcase141a hcase401a hcase430a hcase430b hcase420b hcase410b hcase440b hcase340b hcase331a hcase311a hcase00 hcase01 hcase02 hcase03 hcase30 hcase32
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase401a hcase430b hcase420b hcase410a hcase410b hcase440b hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33
                          omega
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                          ·
                            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                            ·
                              clear hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100b hcase120b hcase130b hcase141a hcase401a hcase401b hcase430a hcase430b hcase420a hcase420b hcase410a hcase410b hcase441a hcase441b hcase310b hcase330b hcase340b hcase00 hcase01 hcase02 hcase03 hcase30 hcase32
                              omega
                            ·
                              clear hn4 hsum_nat0 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100b hcase120b hcase130b hcase141a hcase401a hcase430a hcase430b hcase420b hcase410a hcase410b hcase441a hcase310b hcase330b hcase341a hcase00 hcase01 hcase02 hcase03 hcase30 hcase32
                              omega
                          ·
                            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase100b hcase120b hcase130b hcase141a hcase401a hcase401b hcase430a hcase430b hcase420a hcase420b hcase410a hcase410b hcase310b hcase331a hcase340b hcase00 hcase01 hcase02 hcase03 hcase30 hcase32
                              omega
                            ·
                              clear hn4 hsum_nat0 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase100b hcase120b hcase130b hcase141a hcase401a hcase430b hcase420b hcase410a hcase410b hcase441a hcase310b hcase331a hcase341a hcase00 hcase01 hcase02 hcase03 hcase30 hcase32
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase401a hcase401b hcase430a hcase430b hcase420a hcase420b hcase410a hcase410b hcase441a hcase441b hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase33 hcase34
                          omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          clear hn4 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001b hcase041b hcase110b hcase100b hcase120b hcase130b hcase141a hcase401a hcase401b hcase430a hcase430b hcase420a hcase420b hcase411a hcase411b hcase340b hcase330b hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase44
                          omega
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            clear hn4 hcut11 hcut85 hcut74 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041b hcase110b hcase100b hcase120b hcase130b hcase141a hcase401a hcase430b hcase420b hcase411a hcase340b hcase331a hcase310b hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hcut11 hcut85 hcut74 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase100b hcase120b hcase130b hcase141a hcase401a hcase430a hcase430b hcase420b hcase411a hcase340b hcase331a hcase311a hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase44
                            omega
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase401a hcase401b hcase430a hcase430b hcase420a hcase420b hcase341a hcase310a hcase310b hcase330b hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hcut11 hcut85 hcut74 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase100b hcase120b hcase130b hcase141a hcase401a hcase430a hcase430b hcase420a hcase420b hcase341a hcase310b hcase331a hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase401a hcase401b hcase430a hcase430b hcase420a hcase420b hcase411a hcase411b hcase341a hcase341b hcase00 hcase01 hcase02 hcase03 hcase30 hcase32 hcase33 hcase44
                          omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase401a hcase430a hcase430b hcase421a hcase410b hcase440b hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase401a hcase430a hcase430b hcase421a hcase410a hcase410b hcase441a hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase401a hcase430a hcase430b hcase421a hcase411a hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                      omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase401a hcase431a hcase410b hcase440b hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase401a hcase431a hcase410a hcase410b hcase441a hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase120a hcase120b hcase130a hcase130b hcase141a hcase141b hcase401a hcase431a hcase411a hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                    omega
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100b hcase120b hcase131a hcase140b hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100a hcase100b hcase120b hcase131a hcase141a hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase100b hcase121a hcase140b hcase130b hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100b hcase121a hcase140b hcase131a hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase141a hcase141b hcase130a hcase130b hcase330b hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase100a hcase100b hcase141a hcase141b hcase130a hcase130b hcase331a hcase300b hcase340b hcase310b hcase410b hcase420b hcase430b hcase400b hcase00 hcase01 hcase02 hcase03 hcase32 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase300b hcase340b hcase310b hcase410b hcase420b hcase430b hcase401a hcase00 hcase01 hcase02 hcase03 hcase32 hcase44
                              omega
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase141a hcase141b hcase130a hcase130b hcase331a hcase300a hcase300b hcase340a hcase340b hcase310a hcase310b hcase410b hcase420a hcase420b hcase431a hcase400b hcase00 hcase01 hcase02 hcase03 hcase32 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase300b hcase340b hcase310b hcase410b hcase420a hcase420b hcase431a hcase401a hcase00 hcase01 hcase02 hcase03 hcase32 hcase44
                              omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase141a hcase141b hcase130a hcase130b hcase331a hcase300a hcase300b hcase340a hcase340b hcase310a hcase310b hcase410b hcase421a hcase400b hcase00 hcase01 hcase02 hcase03 hcase32 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase300b hcase340b hcase310b hcase410b hcase421a hcase401a hcase00 hcase01 hcase02 hcase03 hcase32 hcase43 hcase44
                            omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase300a hcase300b hcase340a hcase340b hcase310b hcase411a hcase400b hcase00 hcase01 hcase02 hcase03 hcase32 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              clear hn4 hsum_nat0 hcut11 hcut85 hcut74 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase100a hcase100b hcase121a hcase141a hcase130b hcase331a hcase300b hcase340b hcase310b hcase411a hcase401a hcase420b hcase430b hcase00 hcase01 hcase02 hcase03 hcase32 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase300a hcase300b hcase340a hcase340b hcase310a hcase310b hcase411a hcase401a hcase420a hcase420b hcase431a hcase00 hcase01 hcase02 hcase03 hcase32 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase300a hcase300b hcase340a hcase340b hcase310a hcase310b hcase411a hcase401a hcase421a hcase00 hcase01 hcase02 hcase03 hcase32 hcase43 hcase44
                            omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase300a hcase300b hcase340a hcase340b hcase00 hcase01 hcase02 hcase03 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase300a hcase300b hcase341a hcase341b hcase410b hcase420b hcase430b hcase440b hcase400b hcase00 hcase01 hcase02 hcase03 hcase31 hcase32
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase300a hcase300b hcase410a hcase410b hcase420b hcase430b hcase440b hcase401a hcase00 hcase01 hcase02 hcase03 hcase31 hcase32
                              omega
                          ·
                            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase141a hcase141b hcase130a hcase130b hcase331a hcase300a hcase300b hcase341a hcase341b hcase410b hcase420b hcase430b hcase441a hcase310a hcase310b hcase400b hcase00 hcase01 hcase02 hcase03 hcase32
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase300b hcase341a hcase410a hcase410b hcase420b hcase430b hcase441a hcase310b hcase401a hcase00 hcase01 hcase02 hcase03 hcase32
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase300a hcase300b hcase341a hcase341b hcase410a hcase410b hcase420a hcase420b hcase430a hcase430b hcase441a hcase441b hcase00 hcase01 hcase02 hcase03 hcase32 hcase40
                              omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase141a hcase141b hcase130a hcase130b hcase331a hcase300a hcase300b hcase341a hcase341b hcase410b hcase420a hcase420b hcase431a hcase400b hcase00 hcase01 hcase02 hcase03 hcase31 hcase32 hcase44
                            omega
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase300a hcase300b hcase341a hcase341b hcase410b hcase420a hcase420b hcase431a hcase401a hcase440b hcase00 hcase01 hcase02 hcase03 hcase31 hcase32
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase300a hcase300b hcase341a hcase341b hcase410a hcase410b hcase420a hcase420b hcase431a hcase401a hcase441a hcase00 hcase01 hcase02 hcase03 hcase31 hcase32
                              omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase141a hcase141b hcase130a hcase130b hcase331a hcase300a hcase300b hcase341a hcase341b hcase410b hcase421a hcase400b hcase00 hcase01 hcase02 hcase03 hcase31 hcase32 hcase43 hcase44
                          omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase300a hcase300b hcase341a hcase341b hcase410b hcase421a hcase401a hcase440b hcase00 hcase01 hcase02 hcase03 hcase31 hcase32 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase300a hcase300b hcase341a hcase341b hcase410a hcase410b hcase421a hcase401a hcase441a hcase00 hcase01 hcase02 hcase03 hcase31 hcase32 hcase43
                            omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase300a hcase300b hcase341a hcase411a hcase310b hcase400b hcase00 hcase01 hcase02 hcase03 hcase32 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase300b hcase341a hcase411a hcase310b hcase401a hcase420b hcase430b hcase00 hcase01 hcase02 hcase03 hcase32 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase300a hcase300b hcase341a hcase341b hcase411a hcase310a hcase310b hcase401a hcase420a hcase420b hcase431a hcase00 hcase01 hcase02 hcase03 hcase32 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase300a hcase300b hcase341a hcase341b hcase411a hcase310a hcase310b hcase401a hcase421a hcase00 hcase01 hcase02 hcase03 hcase32 hcase43 hcase44
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase300a hcase300b hcase341a hcase341b hcase411a hcase411b hcase00 hcase01 hcase02 hcase03 hcase32 hcase40 hcase42 hcase43 hcase44
                        omega
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase001a hcase041a hcase110b hcase100b hcase121a hcase141a hcase130b hcase331a hcase310a hcase310b hcase420b hcase430b hcase410b hcase400b hcase00 hcase01 hcase02 hcase03 hcase32 hcase34 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase100b hcase121a hcase141a hcase130b hcase331a hcase310a hcase310b hcase420b hcase430b hcase410b hcase401a hcase00 hcase01 hcase02 hcase03 hcase32 hcase34 hcase44
                            omega
                        ·
                          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase001a hcase041a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase310b hcase420a hcase420b hcase430a hcase430b hcase411a hcase340a hcase340b hcase400b hcase00 hcase01 hcase02 hcase03 hcase32 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase301a hcase310b hcase420b hcase430b hcase411a hcase340b hcase401a hcase00 hcase01 hcase02 hcase03 hcase32 hcase44
                              omega
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase001a hcase041a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase310b hcase420a hcase420b hcase430a hcase430b hcase411a hcase341a hcase400b hcase00 hcase01 hcase02 hcase03 hcase32 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase301a hcase310b hcase420b hcase430b hcase411a hcase341a hcase401a hcase00 hcase01 hcase02 hcase03 hcase32 hcase44
                              omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase001a hcase041a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase310b hcase420a hcase420b hcase431a hcase400b hcase00 hcase01 hcase02 hcase03 hcase32 hcase34 hcase41 hcase44
                          omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase100b hcase121a hcase141a hcase130a hcase130b hcase331a hcase310a hcase310b hcase420a hcase420b hcase431a hcase401a hcase410b hcase00 hcase01 hcase02 hcase03 hcase32 hcase34 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase301a hcase301b hcase310a hcase310b hcase420a hcase420b hcase431a hcase401a hcase411a hcase00 hcase01 hcase02 hcase03 hcase32 hcase34 hcase44
                            omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase001a hcase041a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase310b hcase421a hcase340a hcase340b hcase400b hcase00 hcase01 hcase02 hcase03 hcase32 hcase41 hcase43 hcase44
                          omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat1 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase301a hcase310b hcase421a hcase340b hcase401a hcase410b hcase00 hcase01 hcase02 hcase03 hcase32 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut11 hcut85 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase301a hcase310b hcase421a hcase340b hcase401a hcase411a hcase00 hcase01 hcase02 hcase03 hcase32 hcase43 hcase44
                            omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase001a hcase041a hcase110b hcase100b hcase121a hcase141a hcase130a hcase130b hcase331a hcase310a hcase310b hcase421a hcase341a hcase341b hcase410b hcase400b hcase00 hcase01 hcase02 hcase03 hcase32 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase100b hcase121a hcase141a hcase130a hcase130b hcase331a hcase310a hcase310b hcase421a hcase341a hcase341b hcase410b hcase401a hcase00 hcase01 hcase02 hcase03 hcase32 hcase43 hcase44
                            omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase001a hcase041a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase310b hcase421a hcase341a hcase411a hcase400b hcase00 hcase01 hcase02 hcase03 hcase32 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase301a hcase310b hcase421a hcase341a hcase411a hcase401a hcase00 hcase01 hcase02 hcase03 hcase32 hcase43 hcase44
                            omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100a hcase100b hcase121a hcase121b hcase141a hcase141b hcase130a hcase130b hcase331a hcase331b hcase301a hcase301b hcase00 hcase01 hcase02 hcase03 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase100b hcase121a hcase141a hcase131a hcase00 hcase01 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
      ·
        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031b hcase001b hcase041b hcase110a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310a hcase310b hcase430b hcase440b hcase400b hcase410b hcase420b hcase00 hcase01 hcase02 hcase03 hcase14 hcase30 hcase32 hcase33 hcase34
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310a hcase310b hcase430a hcase430b hcase440b hcase400b hcase410a hcase410b hcase421a hcase00 hcase01 hcase02 hcase03 hcase14 hcase30 hcase32 hcase33 hcase34
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310a hcase310b hcase430a hcase430b hcase440b hcase400b hcase411a hcase00 hcase01 hcase02 hcase03 hcase14 hcase30 hcase32 hcase33 hcase34 hcase42
                      omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                          ·
                            clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031b hcase001b hcase041b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase430b hcase440b hcase401a hcase420b hcase410a hcase410b hcase330b hcase300b hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase34
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase430b hcase440b hcase401a hcase420b hcase410a hcase410b hcase330b hcase301a hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase34
                            omega
                        ·
                          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                          ·
                            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase430b hcase440b hcase401a hcase420b hcase410b hcase331a hcase340b hcase300b hcase00 hcase01 hcase02 hcase03 hcase14 hcase32
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut11 hcut85 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase430b hcase440b hcase401a hcase420b hcase410b hcase331a hcase340b hcase301a hcase00 hcase01 hcase02 hcase03 hcase14 hcase32
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310a hcase310b hcase430b hcase440b hcase401a hcase420b hcase410a hcase410b hcase331a hcase331b hcase00 hcase01 hcase02 hcase03 hcase14 hcase30 hcase32
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310a hcase310b hcase430b hcase440b hcase401a hcase420b hcase411a hcase00 hcase01 hcase02 hcase03 hcase14 hcase30 hcase32 hcase33 hcase34
                        omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310a hcase310b hcase430a hcase430b hcase440b hcase401a hcase421a hcase410b hcase00 hcase01 hcase02 hcase03 hcase14 hcase30 hcase32 hcase33 hcase34
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310a hcase310b hcase430a hcase430b hcase440a hcase440b hcase401a hcase421a hcase411a hcase00 hcase01 hcase02 hcase03 hcase14 hcase30 hcase32 hcase33 hcase34
                        omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase430a hcase430b hcase441a hcase330b hcase300a hcase300b hcase400b hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase34 hcase41 hcase42
                        omega
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031b hcase001b hcase041b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase430a hcase430b hcase441a hcase441b hcase330b hcase300b hcase401a hcase401b hcase340b hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase41 hcase42
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase430a hcase430b hcase441a hcase330b hcase300b hcase401a hcase341a hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase41 hcase42
                          omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase430a hcase430b hcase441a hcase441b hcase330b hcase301a hcase340b hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase40 hcase41 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase430a hcase430b hcase441a hcase441b hcase330b hcase301a hcase341a hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase40 hcase41 hcase42
                        omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase430a hcase430b hcase331a hcase340b hcase00 hcase01 hcase02 hcase03 hcase14 hcase30 hcase32 hcase40 hcase41 hcase42
                      omega
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase430a hcase430b hcase441a hcase331a hcase341a hcase300a hcase300b hcase400b hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase41 hcase42
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase430b hcase441a hcase331a hcase341a hcase300b hcase401a hcase420b hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase41
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310a hcase310b hcase430a hcase430b hcase441a hcase331a hcase331b hcase341a hcase341b hcase300a hcase300b hcase401a hcase421a hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase41
                            omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase001a hcase041a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase430a hcase430b hcase441a hcase331a hcase341a hcase400b hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase41 hcase42
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase430b hcase441a hcase331a hcase341a hcase301a hcase401a hcase420b hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase41
                            omega
                          ·
                            clear hn4 hcut11 hcut85 hcut74 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase041a hcase110b hcase101a hcase120b hcase130b hcase310b hcase430a hcase430b hcase441a hcase331a hcase341a hcase301a hcase401a hcase421a hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase41
                            omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase400a hcase400b hcase330b hcase00 hcase01 hcase02 hcase03 hcase14 hcase30 hcase32 hcase34 hcase41 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase431a hcase400b hcase331a hcase00 hcase01 hcase02 hcase03 hcase14 hcase30 hcase32 hcase34 hcase41 hcase42 hcase44
                    omega
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310a hcase310b hcase401a hcase401b hcase340b hcase300b hcase330b hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase41 hcase42 hcase44
                        omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase431a hcase401a hcase340b hcase300b hcase331a hcase410b hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hcut85 hcut74 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase101a hcase120b hcase130b hcase310b hcase431a hcase401a hcase340b hcase300b hcase331a hcase411a hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase42 hcase44
                          omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310a hcase310b hcase401a hcase401b hcase340b hcase301a hcase410a hcase410b hcase330b hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310b hcase431a hcase401a hcase340b hcase301a hcase410b hcase331a hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase42 hcase44
                          omega
                      ·
                        clear hn4 hcut11 hcut85 hcut74 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase041a hcase110b hcase101a hcase120b hcase130b hcase310b hcase431a hcase401a hcase340a hcase340b hcase301a hcase00 hcase01 hcase02 hcase03 hcase14 hcase32 hcase33 hcase42 hcase44
                        omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hcut85 hcut74 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase110b hcase101a hcase120b hcase130b hcase310a hcase310b hcase431a hcase401a hcase440b hcase00 hcase01 hcase02 hcase03 hcase14 hcase30 hcase32 hcase33 hcase41 hcase42
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase310a hcase310b hcase431a hcase401a hcase341a hcase341b hcase441a hcase00 hcase01 hcase02 hcase03 hcase14 hcase30 hcase32 hcase33 hcase41 hcase42
                      omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase101a hcase101b hcase120a hcase120b hcase130a hcase130b hcase00 hcase01 hcase02 hcase03 hcase14 hcase30 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase101a hcase120b hcase131a hcase00 hcase01 hcase02 hcase03 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
        ·
          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase330b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase331a hcase400b hcase310a hcase310b hcase410b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase32 hcase34 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase400b hcase310b hcase411a hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase32 hcase34 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase331b hcase400a hcase400b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase401a hcase430b hcase410b hcase420b hcase340b hcase310b hcase300b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut11 hcut85 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase401a hcase430b hcase410b hcase420b hcase340b hcase310b hcase301a hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase331b hcase401a hcase401b hcase430a hcase430b hcase410a hcase410b hcase420a hcase420b hcase340a hcase340b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase32 hcase44
                        omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase331b hcase401a hcase430b hcase410a hcase410b hcase420b hcase440b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32
                        omega
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase401a hcase430b hcase410a hcase410b hcase420b hcase341a hcase441a hcase300b hcase310b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase401a hcase430b hcase410a hcase410b hcase420b hcase341a hcase441a hcase300b hcase311a hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32
                            omega
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase401a hcase430b hcase410a hcase410b hcase420b hcase341a hcase441a hcase301a hcase310b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase041a hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase401a hcase430b hcase410a hcase410b hcase420b hcase341a hcase441a hcase301a hcase311a hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32
                            omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase331b hcase401a hcase430a hcase430b hcase410b hcase421a hcase440b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase331b hcase401a hcase430a hcase430b hcase410a hcase410b hcase421a hcase441a hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34
                      omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase401a hcase430b hcase411a hcase300b hcase420b hcase340b hcase310b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase331b hcase401a hcase401b hcase430a hcase430b hcase411a hcase411b hcase300a hcase300b hcase420a hcase420b hcase340a hcase340b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32 hcase44
                          omega
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase401a hcase430b hcase411a hcase300b hcase420b hcase341a hcase310b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase401a hcase430b hcase411a hcase300b hcase420b hcase341a hcase311a hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32 hcase44
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase331b hcase401a hcase430a hcase430b hcase411a hcase300a hcase300b hcase421a hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase31 hcase32 hcase34 hcase44
                      omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase401a hcase430b hcase411a hcase301a hcase310b hcase340b hcase420b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut11 hcut85 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase401a hcase430a hcase430b hcase411a hcase301a hcase310b hcase340b hcase421a hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32 hcase44
                          omega
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase401a hcase430b hcase411a hcase301a hcase310b hcase341a hcase420b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase401a hcase430a hcase430b hcase411a hcase301a hcase310b hcase341a hcase421a hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32 hcase44
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase331b hcase401a hcase401b hcase430a hcase430b hcase411a hcase411b hcase301a hcase301b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase32 hcase34 hcase42 hcase44
                      omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase331b hcase401a hcase431a hcase410b hcase440b hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase331b hcase401a hcase431a hcase410a hcase410b hcase441a hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase110a hcase110b hcase101a hcase101b hcase121a hcase121b hcase331a hcase331b hcase401a hcase431a hcase411a hcase00 hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase44
                  omega
    ·
      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
      ·
        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
        ·
          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
          ·
            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase111a hcase010a hcase010b hcase300b hcase330b hcase340b hcase310b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase111a hcase010a hcase010b hcase300b hcase330b hcase340b hcase311a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase010a hcase010b hcase300b hcase330b hcase341a hcase320b hcase400a hcase400b hcase310b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase111a hcase111b hcase010a hcase010b hcase300a hcase300b hcase330b hcase341a hcase320b hcase400b hcase311a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase010a hcase010b hcase300b hcase330b hcase341a hcase320b hcase401a hcase401b hcase310b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase111a hcase111b hcase010a hcase010b hcase300b hcase330b hcase341a hcase320b hcase401a hcase311a hcase420b hcase440b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase41 hcase43
                        omega
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase111a hcase111b hcase010a hcase010b hcase300b hcase330b hcase341a hcase320b hcase401a hcase311a hcase420b hcase441a hcase430b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase41
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase111a hcase111b hcase010a hcase010b hcase300b hcase330b hcase341a hcase320b hcase401a hcase311a hcase420a hcase420b hcase441a hcase431a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase41
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase111a hcase111b hcase010a hcase010b hcase300a hcase300b hcase330b hcase341a hcase341b hcase320a hcase320b hcase401a hcase401b hcase311a hcase311b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase41 hcase43 hcase44
                      omega
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase111a hcase010a hcase010b hcase300b hcase330b hcase341a hcase321a hcase310b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase111a hcase010a hcase010b hcase300b hcase330b hcase341a hcase321a hcase311a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase010a hcase010b hcase300b hcase331a hcase310b hcase320b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase111a hcase010a hcase010b hcase300b hcase331a hcase310b hcase321a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase111a hcase010a hcase010b hcase300b hcase331a hcase311a hcase340b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase111a hcase010a hcase010b hcase300b hcase331a hcase311a hcase341a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase111a hcase111b hcase010a hcase010b hcase301a hcase310b hcase320b hcase330b hcase340b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase010b hcase301a hcase310b hcase320b hcase330a hcase330b hcase341a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase010b hcase301a hcase310b hcase320b hcase331a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase111a hcase010a hcase010b hcase301a hcase310b hcase321a hcase330b hcase340b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase111a hcase010a hcase010b hcase301a hcase310b hcase321a hcase330a hcase330b hcase341a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase111a hcase010a hcase010b hcase301a hcase310b hcase321a hcase331a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase041a hcase111a hcase010a hcase010b hcase301a hcase311a hcase330b hcase340b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase111a hcase111b hcase010a hcase010b hcase301a hcase311a hcase330b hcase341a hcase320b hcase400b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut22 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase111a hcase111b hcase010b hcase301a hcase311a hcase330b hcase341a hcase320b hcase401a hcase440b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase41 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase041a hcase111a hcase010a hcase010b hcase301a hcase311a hcase330b hcase341a hcase320a hcase320b hcase401a hcase441a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase41 hcase42 hcase43
                      omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase041a hcase111a hcase010a hcase010b hcase301a hcase311a hcase330a hcase330b hcase341a hcase321a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase041a hcase111a hcase010a hcase010b hcase301a hcase311a hcase331a hcase340b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase041a hcase111a hcase010a hcase010b hcase301a hcase311a hcase331a hcase341a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
      ·
        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
        ·
          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase111a hcase320a hcase320b hcase330b hcase300b hcase310b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase001a hcase001b hcase041a hcase041b hcase111a hcase320a hcase320b hcase330b hcase300b hcase311a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase111a hcase111b hcase011a hcase011b hcase320b hcase330b hcase301a hcase310b hcase340b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase001a hcase001b hcase041a hcase041b hcase111a hcase111b hcase011a hcase011b hcase320b hcase330b hcase301a hcase310b hcase341a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase041a hcase111a hcase011a hcase320a hcase320b hcase330b hcase301a hcase311a hcase340b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase041a hcase111a hcase011a hcase320a hcase320b hcase330a hcase330b hcase301a hcase311a hcase341a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase111a hcase320a hcase320b hcase331a hcase300b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase111a hcase011a hcase320a hcase320b hcase331a hcase301a hcase310b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase041a hcase111a hcase011a hcase320a hcase320b hcase331a hcase301a hcase311a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase111a hcase321a hcase300b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase001a hcase041a hcase111a hcase011a hcase321a hcase301a hcase310b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase001a hcase041a hcase111a hcase011a hcase321a hcase301a hcase311a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega

#print axioms symbolic_mask64_integer_shard006
end Jsp404.SixExactFloorKernel
