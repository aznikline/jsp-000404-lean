import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask218_integer_shard011 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut59 : (s00 + s04 + s33 + s40 + s44 + u00 + u04 + u33 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut70 : (s01 + s32 + u01 + u32) + 1 ≤ (s11 + 2))
    (hcut19 : (s11 + s30 + s31 + u11 + u30 + u31 + 1) + 1 ≤ (n))
    (hcut60 : (s40 + s42 + s44 + u40 + u42 + u44) + 1 ≤ (n + 1))
    (hcut17 : (s11 + s31 + u11 + u31 + 2) + 1 ≤ (n))
    (hcut37 : (s03 + s40 + u03 + u40) + 1 ≤ (n))
    (hcut47 : (s04 + s41 + u04 + u41) + 1 ≤ (n))
    (hcut16 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 1))
    (hcut3 : (s44 + u44) + 1 ≤ (s34 + 3))
    (hcut67 : (s02 + s03 + s04 + s10 + s11 + u02 + u03 + u04 + u10 + u11) + 1 ≤ (n + 1))
    (hcut5 : (s00 + s33 + s44 + u00 + u33 + u44) + 1 ≤ (n + 2))
    (hcut57 : (s02 + s42 + u02 + u42) + 1 ≤ (s12 + 2))
    (hcut28 : (s00 + s33 + u00 + u33) + 1 ≤ (n + 1))
    (hcut10 : (s04 + s11 + u04 + u11) + 1 ≤ (n))
    (hcut56 : (s31 + u31) + 1 ≤ (s10 + 1))
    (hcut69 : (s34 + s40 + s41 + s42 + u34 + u40 + u41 + u42) + 1 ≤ (n + 1))
    (hcut75 : (s30 + s34 + s41 + s42 + u30 + u34 + u41 + u42) + 1 ≤ (n + 1))
    (hcut72 : (s00 + s04 + s40 + s44 + u00 + u04 + u40 + u44) + 1 ≤ (2 * n))
    (hcut25 : (s12 + s31 + u12 + u31 + 2) + 1 ≤ (n))
    (hcut71 : (s11 + s13 + s14 + s30 + u11 + u13 + u14 + u30) + 1 ≤ (n))
    (hcut63 : (s43 + u43) + 1 ≤ (s33 + 1))
    (hcut12 : (s03 + s14 + s41 + u03 + u14 + u41) + 1 ≤ (n))
    (hcut62 : (s02 + s03 + s04 + u02 + u03 + u04) + 1 ≤ (n))
    (hcut76 : (s02 + s13 + s14 + s30 + u02 + u13 + u14 + u30) + 1 ≤ (n))
    (hcut73 : (s30 + s31 + s34 + u30 + u31 + u34 + 1) + 1 ≤ (n))
    (hcut0 : (s02 + s11 + s30 + s31 + s34 + s42 + s43 + u02 + u11 + u30 + u31 + u34 + u42 + u43) + 1 ≤ (n + 1))
    (hcut44 : (s02 + s30 + s31 + u02 + u30 + u31 + 1) + 1 ≤ (n))
    (hcut74 : (s03 + s11 + s14 + u03 + u11 + u14) + 1 ≤ (n))
    (hcut61 : (s03 + s04 + u03 + u04 + 1) + 1 ≤ (n))
    (hcut68 : (s01 + s12 + s43 + u01 + u12 + u43) + 1 ≤ (s33 + 2))
    (hcut2 : (s03 + s04 + s40 + s41 + u03 + u04 + u40 + u41) + 1 ≤ (n + 2))
    (hcut58 : (s02 + s11 + s13 + s30 + u02 + u11 + u13 + u30) + 1 ≤ (n))
    (hcut48 : (s02 + s11 + s13 + s31 + u02 + u11 + u13 + u31 + 1) + 1 ≤ (n))
    (hcut33 : (s40 + s41 + s42 + u40 + u41 + u42) + 1 ≤ (n))
    (hcut32 : (s30 + u30 + 2) + 1 ≤ (n))
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
    (hcase121a : 1 ≤ s12)
    (hcase121b : u12 = 1)
    (hcase311a : 1 ≤ s31)
    (hcase311b : u31 = 1)
    : False := by
  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
  ·
    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
    ·
      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase330b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
      ·
        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
        ·
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase300a hcase300b hcase040a hcase040b hcase320a hcase320b hcase010a hcase010b hcase420b hcase400b hcase410b hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase43 hcase44
                      omega
                    ·
                      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase020b hcase340b hcase331a hcase300b hcase040b hcase320b hcase010b hcase420a hcase420b hcase400a hcase400b hcase411a hcase411b hcase030b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase340a hcase340b hcase331a hcase300a hcase300b hcase040b hcase320a hcase320b hcase010a hcase010b hcase420b hcase400b hcase411a hcase031a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase43 hcase44
                        omega
                  ·
                    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut10 hcut56 hcut69 hcut75 hcut72 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase020b hcase340b hcase331a hcase300b hcase040b hcase320b hcase010b hcase420a hcase420b hcase401a hcase401b hcase030b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase41 hcase43 hcase44
                      omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase340a hcase340b hcase331a hcase300a hcase300b hcase040b hcase320a hcase320b hcase010a hcase010b hcase420b hcase401a hcase031a hcase410b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase300a hcase300b hcase040a hcase040b hcase320a hcase320b hcase010a hcase010b hcase420a hcase420b hcase401a hcase031a hcase031b hcase411a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase43 hcase44
                        omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut10 hcut56 hcut69 hcut75 hcut72 hcut71 hcut63 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase311a hcase020a hcase020b hcase340b hcase331a hcase300b hcase040b hcase320b hcase010b hcase421a hcase440b hcase430b hcase400b hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase41
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase300a hcase300b hcase040a hcase040b hcase320a hcase320b hcase010a hcase010b hcase421a hcase440a hcase440b hcase430a hcase430b hcase401a hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase41
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase300a hcase300b hcase040a hcase040b hcase320a hcase320b hcase010a hcase010b hcase421a hcase440a hcase440b hcase431a hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41
                      omega
                  ·
                    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                    ·
                      clear hn4 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121b hcase311a hcase020b hcase340b hcase331a hcase300b hcase040b hcase320b hcase010b hcase421a hcase421b hcase030b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase43
                      omega
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase121a hcase121b hcase311a hcase020a hcase020b hcase340b hcase331a hcase300b hcase040a hcase040b hcase320b hcase010a hcase010b hcase421a hcase421b hcase031a hcase031b hcase100b hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut57 hcut28 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase311a hcase020a hcase020b hcase340b hcase331a hcase300b hcase040a hcase040b hcase320b hcase010b hcase421a hcase421b hcase031a hcase101a hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase43
                        omega
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  clear hn4 hsum_nat4 hcut59 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121b hcase311a hcase020b hcase340b hcase331a hcase300b hcase040b hcase320a hcase320b hcase011a hcase030b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase300a hcase300b hcase040a hcase040b hcase320a hcase320b hcase011a hcase031a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase300a hcase300b hcase040a hcase040b hcase321a hcase321b hcase100b hcase00 hcase01 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  clear hn4 hsum_nat4 hcut59 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121b hcase311a hcase020b hcase340b hcase331a hcase300b hcase040b hcase321a hcase101a hcase101b hcase030b hcase00 hcase01 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase300a hcase300b hcase040a hcase040b hcase101a hcase101b hcase031a hcase031b hcase110b hcase00 hcase01 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut59 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut5 hcut57 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase311a hcase020a hcase020b hcase340b hcase331a hcase300b hcase040a hcase040b hcase321a hcase101a hcase031a hcase111a hcase00 hcase01 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase300a hcase300b hcase041a hcase041b hcase100b hcase00 hcase01 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase300a hcase300b hcase041a hcase041b hcase101a hcase101b hcase030a hcase030b hcase010a hcase010b hcase110a hcase110b hcase320a hcase320b hcase410b hcase420b hcase400b hcase00 hcase12 hcase13 hcase14 hcase31 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase340a hcase340b hcase331a hcase300a hcase300b hcase041a hcase101a hcase101b hcase030b hcase010a hcase010b hcase110a hcase110b hcase320a hcase320b hcase410b hcase420b hcase401a hcase00 hcase12 hcase13 hcase14 hcase31 hcase43 hcase44
                            omega
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            clear hn4 hsum_nat1 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase311a hcase020a hcase020b hcase340b hcase331a hcase300b hcase041a hcase101a hcase101b hcase030b hcase010b hcase110a hcase110b hcase320b hcase410b hcase421a hcase430b hcase00 hcase12 hcase13 hcase14 hcase31 hcase40 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase300a hcase300b hcase041a hcase041b hcase101a hcase101b hcase030a hcase030b hcase010a hcase010b hcase110a hcase110b hcase320a hcase320b hcase410a hcase410b hcase421a hcase431a hcase00 hcase12 hcase13 hcase14 hcase31 hcase40 hcase44
                            omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase340a hcase340b hcase331a hcase300a hcase300b hcase041a hcase101a hcase101b hcase030b hcase010a hcase010b hcase110a hcase110b hcase320a hcase320b hcase411a hcase400b hcase420b hcase00 hcase12 hcase13 hcase14 hcase31 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase300a hcase300b hcase041a hcase041b hcase101a hcase101b hcase030a hcase030b hcase010a hcase010b hcase110a hcase110b hcase320a hcase320b hcase411a hcase400a hcase400b hcase421a hcase00 hcase12 hcase13 hcase14 hcase31 hcase43 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase300a hcase300b hcase041a hcase041b hcase101a hcase101b hcase030a hcase030b hcase010a hcase010b hcase110a hcase110b hcase320a hcase320b hcase411a hcase401a hcase00 hcase12 hcase13 hcase14 hcase31 hcase42 hcase43 hcase44
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase300a hcase300b hcase041a hcase041b hcase101a hcase101b hcase030a hcase030b hcase010a hcase010b hcase110b hcase00 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut5 hcut57 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase311a hcase020a hcase020b hcase340b hcase331a hcase300b hcase041a hcase101a hcase030a hcase030b hcase010b hcase320b hcase00 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut59 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut5 hcut57 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase311a hcase020a hcase020b hcase340b hcase331a hcase300b hcase041a hcase101a hcase030a hcase030b hcase010a hcase010b hcase111a hcase321a hcase00 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase300a hcase300b hcase041a hcase101a hcase101b hcase030a hcase030b hcase011a hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase300a hcase300b hcase041a hcase101a hcase101b hcase031a hcase00 hcase01 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase301a hcase301b hcase400b hcase410b hcase420b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut67 hcut5 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase301b hcase400b hcase410b hcase421a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43 hcase44
                omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut16 hcut3 hcut67 hcut5 hcut57 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase340a hcase340b hcase331a hcase301a hcase301b hcase400b hcase411a hcase420b hcase440b hcase030b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43
                    omega
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase340a hcase340b hcase331a hcase301a hcase301b hcase400b hcase411a hcase420b hcase440b hcase031a hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase301a hcase301b hcase400a hcase400b hcase411a hcase411b hcase420a hcase420b hcase440a hcase440b hcase031a hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43
                      omega
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase340a hcase340b hcase331a hcase301a hcase301b hcase400b hcase411a hcase420b hcase441a hcase030b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43
                    omega
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase340a hcase340b hcase331a hcase301a hcase301b hcase400b hcase411a hcase420b hcase441a hcase031a hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase301a hcase301b hcase400a hcase400b hcase411a hcase411b hcase420a hcase420b hcase441a hcase441b hcase031a hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43
                      omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase301a hcase301b hcase400a hcase400b hcase411a hcase421a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43 hcase44
                omega
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase340a hcase340b hcase331a hcase301a hcase301b hcase401a hcase410b hcase420b hcase440b hcase040b hcase00 hcase01 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43
                    omega
                  ·
                    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase340a hcase340b hcase331a hcase301a hcase301b hcase401a hcase410b hcase420b hcase440a hcase440b hcase041a hcase030b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase301a hcase301b hcase401a hcase401b hcase410a hcase410b hcase420a hcase420b hcase440a hcase440b hcase041a hcase031a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43
                      omega
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase340a hcase340b hcase331a hcase301a hcase301b hcase401a hcase410b hcase420b hcase441a hcase030b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43
                    omega
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase340a hcase340b hcase331a hcase301a hcase301b hcase401a hcase410b hcase420b hcase441a hcase031a hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase301a hcase301b hcase401a hcase401b hcase410a hcase410b hcase420a hcase420b hcase441a hcase441b hcase031a hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43
                      omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase301a hcase301b hcase401a hcase410a hcase410b hcase421a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase340a hcase340b hcase331a hcase331b hcase301a hcase301b hcase401a hcase411a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase42 hcase43 hcase44
              omega
    ·
      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase330b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
      ·
        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
        ·
          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase020a hcase020b hcase341a hcase341b hcase331a hcase331b hcase320a hcase320b hcase010a hcase010b hcase400a hcase400b hcase430a hcase430b hcase100b hcase00 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase41 hcase42 hcase44
                  omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase320a hcase320b hcase010a hcase010b hcase400b hcase430b hcase101a hcase101b hcase410b hcase040a hcase040b hcase420b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase44
                        omega
                      ·
                        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase020a hcase020b hcase341a hcase341b hcase320a hcase320b hcase010b hcase400b hcase430b hcase101a hcase101b hcase410b hcase040b hcase421a hcase030b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut57 hcut28 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase020a hcase020b hcase341a hcase331a hcase320b hcase010b hcase400b hcase430a hcase430b hcase101a hcase410b hcase040a hcase040b hcase421a hcase031a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase44
                          omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut57 hcut28 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase020a hcase020b hcase341a hcase341b hcase320a hcase320b hcase010b hcase400b hcase430b hcase101a hcase410b hcase041a hcase420b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut57 hcut28 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase020a hcase020b hcase341a hcase331a hcase320b hcase010b hcase400b hcase430a hcase430b hcase101a hcase410b hcase041a hcase421a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase44
                        omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase331a hcase331b hcase320a hcase320b hcase010a hcase010b hcase400a hcase400b hcase430b hcase101a hcase101b hcase411a hcase420a hcase420b hcase440b hcase00 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31
                        omega
                      ·
                        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase311a hcase311b hcase020b hcase341a hcase341b hcase320a hcase320b hcase010b hcase400b hcase430b hcase101a hcase101b hcase411a hcase420b hcase441a hcase030b hcase00 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31
                          omega
                        ·
                          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase311a hcase311b hcase020b hcase341a hcase341b hcase320a hcase320b hcase010b hcase400b hcase430b hcase101a hcase101b hcase411a hcase420b hcase441a hcase031a hcase040b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase331a hcase331b hcase320a hcase320b hcase010a hcase010b hcase400a hcase400b hcase430a hcase430b hcase101a hcase101b hcase411a hcase411b hcase420a hcase420b hcase441a hcase441b hcase031a hcase041a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31
                            omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase331a hcase331b hcase320a hcase320b hcase010a hcase010b hcase400a hcase400b hcase430a hcase430b hcase101a hcase101b hcase411a hcase421a hcase00 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase44
                      omega
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut16 hcut3 hcut67 hcut5 hcut57 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase341a hcase341b hcase331a hcase320a hcase320b hcase010a hcase010b hcase400b hcase431a hcase440b hcase420b hcase030b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase41
                      omega
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase341a hcase341b hcase331a hcase320a hcase320b hcase010a hcase010b hcase400b hcase431a hcase440b hcase420b hcase031a hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase41
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase331a hcase331b hcase320a hcase320b hcase010a hcase010b hcase400a hcase400b hcase431a hcase431b hcase440a hcase440b hcase420a hcase420b hcase031a hcase041a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase41
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase331a hcase331b hcase320a hcase320b hcase010a hcase010b hcase400a hcase400b hcase431a hcase440a hcase440b hcase421a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase41
                    omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase121a hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase331a hcase320a hcase320b hcase010a hcase010b hcase400b hcase431a hcase441a hcase410b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase42
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase331a hcase331b hcase320a hcase320b hcase010a hcase010b hcase400a hcase400b hcase431a hcase441a hcase441b hcase411a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase42
                    omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase311a hcase311b hcase020b hcase341a hcase341b hcase320a hcase320b hcase010b hcase401a hcase401b hcase410a hcase410b hcase440a hcase440b hcase420a hcase420b hcase030b hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase341a hcase341b hcase331a hcase320a hcase320b hcase010a hcase010b hcase401a hcase410b hcase440a hcase440b hcase420b hcase030b hcase041a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase43
                        omega
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase341a hcase341b hcase331a hcase320a hcase320b hcase010a hcase010b hcase401a hcase410b hcase440b hcase420b hcase031a hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase331a hcase331b hcase320a hcase320b hcase010a hcase010b hcase401a hcase401b hcase410a hcase410b hcase440a hcase440b hcase420a hcase420b hcase031a hcase041a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase43
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase331a hcase331b hcase320a hcase320b hcase010a hcase010b hcase401a hcase410a hcase410b hcase440a hcase440b hcase421a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase43
                    omega
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase311a hcase311b hcase020b hcase341a hcase341b hcase320a hcase320b hcase010b hcase401a hcase401b hcase410a hcase410b hcase030b hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase42 hcase43
                      omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase341a hcase341b hcase331a hcase320a hcase320b hcase010a hcase010b hcase401a hcase410b hcase441a hcase030b hcase041a hcase420b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase331a hcase331b hcase320a hcase320b hcase010a hcase010b hcase401a hcase410a hcase410b hcase441a hcase441b hcase030a hcase030b hcase041a hcase041b hcase421a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase43
                        omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut59 hcut70 hcut19 hcut60 hcut17 hcut47 hcut16 hcut3 hcut67 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase341a hcase341b hcase331a hcase320a hcase320b hcase010a hcase010b hcase401a hcase410b hcase441a hcase031a hcase420b hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase331a hcase331b hcase320a hcase320b hcase010a hcase010b hcase401a hcase401b hcase410a hcase410b hcase441a hcase441b hcase031a hcase420a hcase420b hcase041a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase43
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase331a hcase331b hcase320a hcase320b hcase010a hcase010b hcase401a hcase410a hcase410b hcase441a hcase441b hcase031a hcase031b hcase421a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase43
                      omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase331a hcase331b hcase320a hcase320b hcase010a hcase010b hcase401a hcase411a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase311a hcase311b hcase020b hcase341a hcase341b hcase331a hcase320a hcase320b hcase011a hcase030b hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase331a hcase331b hcase320a hcase320b hcase011a hcase030a hcase030b hcase041a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase020a hcase020b hcase341a hcase341b hcase331a hcase331b hcase320a hcase320b hcase011a hcase031a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase020a hcase020b hcase341a hcase331a hcase321a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
  ·
    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
    ·
      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
      ·
        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase021a hcase021b hcase030a hcase030b hcase300a hcase300b hcase100b hcase00 hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut67 hcut5 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase311b hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase410b hcase400b hcase00 hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase311a hcase311b hcase021a hcase021b hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase410a hcase410b hcase401a hcase401b hcase040a hcase040b hcase010a hcase010b hcase320a hcase320b hcase330b hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase311a hcase021a hcase030b hcase300b hcase101a hcase101b hcase410a hcase410b hcase401a hcase401b hcase040b hcase010b hcase320b hcase331a hcase340b hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut10 hcut56 hcut75 hcut72 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase311a hcase021a hcase030b hcase300b hcase101a hcase101b hcase410a hcase410b hcase401a hcase040b hcase010b hcase320b hcase331a hcase341a hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase021a hcase021b hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase410a hcase410b hcase401a hcase401b hcase040a hcase040b hcase010a hcase010b hcase110b hcase00 hcase12 hcase13 hcase14 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut59 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase410a hcase410b hcase401a hcase401b hcase040a hcase040b hcase010a hcase010b hcase321a hcase111a hcase330b hcase00 hcase12 hcase13 hcase14 hcase31 hcase34 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat4 hcut59 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase311a hcase021a hcase030b hcase300b hcase101a hcase101b hcase410a hcase410b hcase401a hcase401b hcase040b hcase010a hcase010b hcase321a hcase111a hcase331a hcase340b hcase00 hcase12 hcase13 hcase14 hcase31 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase021a hcase021b hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase410a hcase410b hcase401a hcase401b hcase040a hcase040b hcase010a hcase010b hcase321a hcase111a hcase111b hcase331a hcase341a hcase00 hcase12 hcase13 hcase14 hcase31 hcase42 hcase43 hcase44
                          omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase021a hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase410a hcase410b hcase401a hcase401b hcase040a hcase040b hcase011a hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase021a hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase410a hcase410b hcase401a hcase401b hcase041a hcase00 hcase01 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase311a hcase311b hcase021a hcase021b hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase411a hcase411b hcase110a hcase110b hcase320a hcase320b hcase440a hcase440b hcase330b hcase00 hcase01 hcase04 hcase12 hcase13 hcase14 hcase31 hcase34 hcase40 hcase42 hcase43
                    omega
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        clear hn4 hsum_nat1 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut10 hcut56 hcut75 hcut72 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase311a hcase021a hcase030b hcase300b hcase101a hcase101b hcase411a hcase110a hcase110b hcase320b hcase440b hcase331a hcase040b hcase010b hcase00 hcase12 hcase13 hcase14 hcase31 hcase34 hcase40 hcase42 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase021a hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase411a hcase411b hcase110a hcase110b hcase320a hcase320b hcase440a hcase440b hcase331a hcase331b hcase040a hcase040b hcase011a hcase00 hcase12 hcase13 hcase14 hcase31 hcase34 hcase40 hcase42 hcase43
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase021a hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase411a hcase411b hcase110a hcase110b hcase320a hcase320b hcase440a hcase440b hcase331a hcase331b hcase041a hcase00 hcase01 hcase12 hcase13 hcase14 hcase31 hcase34 hcase40 hcase42 hcase43
                      omega
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase311a hcase311b hcase021a hcase021b hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase411a hcase411b hcase110a hcase110b hcase320a hcase320b hcase441a hcase441b hcase040a hcase040b hcase330b hcase00 hcase01 hcase12 hcase13 hcase14 hcase31 hcase34 hcase40 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase311a hcase311b hcase021a hcase030b hcase300a hcase300b hcase101a hcase101b hcase411a hcase411b hcase110a hcase110b hcase320a hcase320b hcase040b hcase331a hcase00 hcase01 hcase12 hcase13 hcase14 hcase31 hcase34 hcase40 hcase42 hcase43
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase021a hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase411a hcase411b hcase110a hcase110b hcase320a hcase320b hcase441a hcase441b hcase041a hcase00 hcase01 hcase12 hcase13 hcase14 hcase31 hcase33 hcase34 hcase40 hcase42 hcase43
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase021a hcase021b hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase411a hcase411b hcase110b hcase00 hcase01 hcase04 hcase12 hcase13 hcase14 hcase31 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase311a hcase311b hcase021a hcase021b hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase411a hcase411b hcase111a hcase111b hcase330b hcase00 hcase01 hcase04 hcase12 hcase13 hcase14 hcase31 hcase32 hcase34 hcase40 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut5 hcut57 hcut10 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase311a hcase021a hcase030a hcase030b hcase300b hcase101a hcase411a hcase411b hcase331a hcase320b hcase010b hcase340b hcase00 hcase04 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        clear hn4 hsum_nat1 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut57 hcut10 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase311a hcase021a hcase030b hcase300b hcase101a hcase411a hcase331a hcase320b hcase010b hcase341a hcase040b hcase00 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase021a hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase411a hcase411b hcase111a hcase111b hcase331a hcase331b hcase320a hcase320b hcase010a hcase010b hcase341a hcase341b hcase041a hcase00 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase021a hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase411a hcase411b hcase111a hcase111b hcase331a hcase331b hcase320a hcase320b hcase011a hcase00 hcase04 hcase12 hcase13 hcase14 hcase31 hcase34 hcase40 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut59 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase311a hcase021a hcase030b hcase300b hcase101a hcase101b hcase411a hcase411b hcase111a hcase331a hcase321a hcase040b hcase340b hcase00 hcase01 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase021a hcase021b hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase411a hcase411b hcase111a hcase111b hcase331a hcase321a hcase040a hcase040b hcase341a hcase00 hcase01 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase021a hcase030a hcase030b hcase300a hcase300b hcase101a hcase101b hcase411a hcase411b hcase111a hcase111b hcase331a hcase331b hcase321a hcase321b hcase041a hcase00 hcase01 hcase12 hcase13 hcase14 hcase31 hcase34 hcase40 hcase42 hcase43 hcase44
                    omega
      ·
        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase311a hcase311b hcase021a hcase021b hcase030a hcase030b hcase301a hcase301b hcase330b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase121a hcase121b hcase311a hcase021a hcase030b hcase301a hcase331a hcase040b hcase320b hcase010b hcase340b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase021a hcase021b hcase030a hcase030b hcase301a hcase331a hcase040a hcase040b hcase320a hcase320b hcase010a hcase010b hcase341a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase021a hcase030a hcase030b hcase301a hcase301b hcase331a hcase331b hcase040a hcase040b hcase320a hcase320b hcase011a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase021a hcase021b hcase030a hcase030b hcase301a hcase331a hcase040a hcase040b hcase321a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase021a hcase030a hcase030b hcase301a hcase301b hcase331a hcase331b hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut59 hcut70 hcut19 hcut60 hcut17 hcut37 hcut47 hcut16 hcut3 hcut67 hcut5 hcut57 hcut28 hcut10 hcut56 hcut69 hcut75 hcut72 hcut25 hcut71 hcut63 hcut12 hcut62 hcut76 hcut73 hcut0 hcut44 hcut74 hcut61 hcut68 hcut2 hcut58 hcut48 hcut33 hcut32 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase121a hcase121b hcase311a hcase311b hcase021a hcase031a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega

#print axioms symbolic_v2_mask218_integer_shard011
end Jsp404.SixExactFloorKernel
