import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_mask64_integer_shard005 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
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
    (hcase000a : s00 = 0)
    (hcase000b : u00 = 0)
    : False := by
  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
  ·
    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
    ·
      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
      ·
        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase130b hcase120b hcase110b hcase100b hcase140b hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase010b hcase040b hcase130b hcase120b hcase110b hcase100b hcase141a hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase000b hcase010b hcase040b hcase130a hcase130b hcase120a hcase120b hcase110a hcase110b hcase00 hcase02 hcase03 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      clear hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase130a hcase130b hcase120a hcase120b hcase111a hcase111b hcase330b hcase320b hcase310b hcase340b hcase300b hcase00 hcase02 hcase03 hcase10 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase010b hcase040b hcase130a hcase130b hcase120a hcase120b hcase111a hcase111b hcase330b hcase320b hcase310b hcase340a hcase340b hcase301a hcase00 hcase02 hcase03 hcase10 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase010b hcase040b hcase130a hcase130b hcase120a hcase120b hcase111a hcase111b hcase330b hcase320b hcase310b hcase341a hcase00 hcase02 hcase03 hcase10 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase130a hcase130b hcase120a hcase120b hcase111a hcase111b hcase330b hcase320b hcase311a hcase340b hcase300b hcase00 hcase02 hcase03 hcase10 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase010b hcase040b hcase130a hcase130b hcase120a hcase120b hcase111a hcase111b hcase330b hcase320b hcase311a hcase340a hcase340b hcase301a hcase00 hcase02 hcase03 hcase10 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase010b hcase040b hcase130a hcase130b hcase120a hcase120b hcase111a hcase111b hcase330b hcase320b hcase311a hcase341a hcase00 hcase02 hcase03 hcase10 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase130a hcase130b hcase120a hcase120b hcase111a hcase111b hcase330b hcase321a hcase300b hcase340b hcase310b hcase00 hcase02 hcase03 hcase10 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase130a hcase130b hcase120a hcase120b hcase111a hcase111b hcase330b hcase321a hcase300b hcase340b hcase311a hcase00 hcase02 hcase03 hcase10 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase010b hcase040b hcase130a hcase130b hcase120a hcase120b hcase111a hcase111b hcase330a hcase330b hcase321a hcase321b hcase300a hcase300b hcase00 hcase02 hcase03 hcase10 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase010b hcase040a hcase040b hcase130a hcase130b hcase120a hcase120b hcase111a hcase111b hcase330a hcase330b hcase321a hcase321b hcase00 hcase02 hcase03 hcase10 hcase14 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase130b hcase120b hcase111a hcase100b hcase140b hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase010b hcase040b hcase130b hcase120b hcase111a hcase100b hcase141a hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase000b hcase010b hcase040b hcase130a hcase130b hcase120a hcase120b hcase111a hcase111b hcase331a hcase331b hcase00 hcase02 hcase03 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase130b hcase121a hcase100b hcase110b hcase140b hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase010b hcase040b hcase130a hcase130b hcase121a hcase121b hcase100a hcase100b hcase110a hcase110b hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase130a hcase130b hcase100a hcase100b hcase111a hcase111b hcase140a hcase140b hcase330b hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase130b hcase121a hcase100b hcase111a hcase140b hcase331a hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase010b hcase040b hcase130a hcase130b hcase121a hcase121b hcase100a hcase100b hcase111a hcase111b hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase000b hcase010b hcase040b hcase130a hcase130b hcase121a hcase121b hcase00 hcase02 hcase03 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
      ·
        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase131a hcase131b hcase100a hcase100b hcase140a hcase140b hcase120a hcase120b hcase340b hcase320b hcase300b hcase310b hcase330b hcase00 hcase02 hcase03 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase131a hcase100b hcase140b hcase120b hcase340a hcase340b hcase320a hcase320b hcase300a hcase300b hcase310a hcase310b hcase331a hcase331b hcase110b hcase00 hcase02 hcase03 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase131a hcase100b hcase140b hcase120b hcase340b hcase320b hcase300b hcase310b hcase331a hcase111a hcase00 hcase02 hcase03 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase131a hcase100b hcase140b hcase120b hcase340a hcase340b hcase320a hcase320b hcase300a hcase300b hcase110b hcase00 hcase02 hcase03 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase100a hcase100b hcase140a hcase140b hcase120a hcase120b hcase340b hcase320b hcase300b hcase311a hcase111a hcase111b hcase330b hcase00 hcase02 hcase03 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase131a hcase100b hcase140b hcase120b hcase340b hcase320b hcase300b hcase311a hcase111a hcase331a hcase00 hcase02 hcase03 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase010b hcase040a hcase040b hcase131a hcase131b hcase100a hcase100b hcase140a hcase140b hcase120a hcase120b hcase340a hcase340b hcase320a hcase320b hcase00 hcase02 hcase03 hcase11 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase131b hcase100a hcase100b hcase140a hcase140b hcase120a hcase120b hcase340b hcase321a hcase300b hcase330b hcase00 hcase02 hcase03 hcase11 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase131a hcase131b hcase100a hcase100b hcase140a hcase140b hcase120a hcase120b hcase340a hcase340b hcase300a hcase300b hcase331a hcase331b hcase310a hcase310b hcase110b hcase00 hcase02 hcase03 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase131a hcase131b hcase100a hcase100b hcase140a hcase140b hcase120a hcase120b hcase340b hcase321a hcase300b hcase331a hcase310b hcase111a hcase00 hcase02 hcase03 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                      ·
                        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase131a hcase131b hcase100a hcase100b hcase140a hcase140b hcase120a hcase120b hcase340a hcase340b hcase300a hcase300b hcase331a hcase331b hcase110b hcase00 hcase02 hcase03 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase131a hcase131b hcase100a hcase100b hcase140a hcase140b hcase120a hcase120b hcase340b hcase321a hcase300b hcase331a hcase311a hcase111a hcase00 hcase02 hcase03 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase010b hcase040a hcase040b hcase131a hcase131b hcase100a hcase100b hcase140a hcase140b hcase120a hcase120b hcase340a hcase340b hcase321a hcase321b hcase00 hcase02 hcase03 hcase11 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase010b hcase040b hcase131a hcase131b hcase100a hcase100b hcase140a hcase140b hcase120a hcase120b hcase00 hcase02 hcase03 hcase11 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase100a hcase100b hcase140a hcase140b hcase330b hcase00 hcase02 hcase03 hcase11 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase131a hcase100b hcase140b hcase121a hcase331a hcase331b hcase110b hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase010a hcase010b hcase040a hcase040b hcase131a hcase100b hcase140b hcase121a hcase331a hcase111a hcase00 hcase02 hcase03 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
          ·
            clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase010b hcase040b hcase131a hcase131b hcase100a hcase100b hcase00 hcase02 hcase03 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
        ·
          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase000b hcase010b hcase040b hcase131a hcase131b hcase00 hcase02 hcase03 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
    ·
      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase000b hcase010b hcase041a hcase00 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega
  ·
    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
    ·
      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
      ·
        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase310a hcase310b hcase330a hcase330b hcase040a hcase040b hcase300a hcase300b hcase110b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase310b hcase330b hcase040a hcase040b hcase300b hcase111a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            clear hn4 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase011a hcase310b hcase330b hcase040b hcase301a hcase00 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase310a hcase310b hcase330a hcase330b hcase041a hcase041b hcase110b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase30 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase310b hcase330b hcase041a hcase041b hcase111a hcase300b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase011a hcase310b hcase330b hcase041a hcase111a hcase301a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
      ·
        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase310a hcase310b hcase331a hcase331b hcase340a hcase340b hcase110b hcase00 hcase02 hcase03 hcase04 hcase10 hcase12 hcase13 hcase14 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase310b hcase331a hcase340b hcase111a hcase300b hcase00 hcase02 hcase03 hcase04 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase011a hcase310b hcase331a hcase340b hcase111a hcase301a hcase00 hcase02 hcase03 hcase04 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase310a hcase310b hcase331a hcase331b hcase341a hcase341b hcase300a hcase300b hcase110b hcase00 hcase02 hcase03 hcase04 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase310b hcase331a hcase341a hcase300b hcase111a hcase00 hcase02 hcase03 hcase04 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut62 hcut70 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000b hcase011a hcase310b hcase331a hcase341a hcase301a hcase040b hcase00 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase310a hcase310b hcase331a hcase331b hcase341a hcase341b hcase301a hcase301b hcase041a hcase041b hcase110b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut70 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase000a hcase000b hcase011a hcase310b hcase331a hcase341a hcase301a hcase041a hcase111a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
    ·
      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
      ·
        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase311a hcase340b hcase330b hcase300b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            clear hn4 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase000b hcase011a hcase311a hcase340b hcase330b hcase301a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase340a hcase340b hcase331a hcase331b hcase110b hcase00 hcase02 hcase03 hcase04 hcase10 hcase12 hcase13 hcase14 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase311a hcase340b hcase331a hcase111a hcase300b hcase00 hcase02 hcase03 hcase04 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase000b hcase011a hcase311a hcase340b hcase331a hcase111a hcase301a hcase00 hcase02 hcase03 hcase04 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
      ·
        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase341a hcase341b hcase040a hcase040b hcase110b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase000b hcase011a hcase311a hcase040b hcase111a hcase330b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut62 hcut54 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase000b hcase011a hcase311a hcase341a hcase040b hcase111a hcase331a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase311a hcase341a hcase041a hcase041b hcase300b hcase330b hcase00 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase341a hcase341b hcase041a hcase041b hcase300a hcase300b hcase331a hcase331b hcase110b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut86 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase311a hcase341a hcase041a hcase041b hcase300b hcase331a hcase111a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase000b hcase011a hcase311a hcase341a hcase041a hcase301a hcase330b hcase00 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut1 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase000b hcase011a hcase341a hcase341b hcase041a hcase331a hcase331b hcase110b hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut85 hcut74 hcut4 hcut23 hcut44 hcut50 hcut37 hcut0 hcut22 hcut60 hcut65 hcut75 hcut72 hcut57 hcut55 hcut62 hcut54 hcut5 hcut40 hcut36 hcut26 hcut45 hcut30 hcut61 hcut71 hcut31 hcut18 hcut68 hcut64 hcut3 hcut77 hcut63 hcut17 hcut76 hcut51 hcut24 hcut16 hcut73 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase000a hcase000b hcase011a hcase311a hcase341a hcase041a hcase301a hcase331a hcase111a hcase00 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega

#print axioms symbolic_mask64_integer_shard005
end Jsp404.SixExactFloorKernel
