import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask254_integer_shard001 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut62 : (s02 + s11 + s13 + s14 + s31 + s33 + u02 + u11 + u13 + u14 + u31 + u33) + 1 ≤ (n))
    (hcut53 : (s01 + u01) + 1 ≤ (s33 + 2))
    (hcut2 : (s34 + u34) + 1 ≤ (s44 + 2))
    (hcut64 : (s10 + s32 + s44 + u10 + u32 + u44) + 1 ≤ (n + 2))
    (hcut58 : (s02 + s10 + s13 + s14 + s33 + u02 + u10 + u13 + u14 + u33) + 1 ≤ (n))
    (hcut41 : (s33 + s34 + s40 + u33 + u34 + u40) + 1 ≤ (n + 1))
    (hcut6 : (s11 + s42 + u11 + u42) + 1 ≤ (s32 + 2))
    (hcut7 : (s32 + s43 + u32 + u43) + 1 ≤ (s00 + 1))
    (hcut59 : (s02 + s04 + s10 + s32 + u02 + u04 + u10 + u32) + 1 ≤ (n))
    (hcut63 : (s02 + s10 + s13 + s14 + s33 + s41 + u02 + u10 + u13 + u14 + u33 + u41) + 1 ≤ (n + s31 + 3))
    (hcut66 : (s30 + s32 + s33 + s34 + u30 + u32 + u33 + u34) + 1 ≤ (n + 1))
    (hcut16 : (s34 + s40 + u34 + u40) + 1 ≤ (n))
    (hcut47 : (s03 + s04 + s10 + s11 + s33 + u03 + u04 + u10 + u11 + u33) + 1 ≤ (n + 1))
    (hcut5 : (s00 + s03 + s04 + s12 + s40 + s41 + s44 + u00 + u03 + u04 + u12 + u40 + u41 + u44) + 1 ≤ (2 * n + 2))
    (hcut50 : (s01 + s34 + s43 + u01 + u34 + u43) + 1 ≤ (n))
    (hcut3 : (s30 + s31 + u30 + u31) + 1 ≤ (s10 + 2))
    (hcut8 : (s02 + u02) + 1 ≤ (s34))
    (hcut19 : (s40 + s41 + s42 + s43 + s44 + u40 + u41 + u42 + u43 + u44) + 1 ≤ (n + 1))
    (hcut12 : (s42 + u42) + 1 ≤ (s12 + 1))
    (hcut21 : (s10 + s43 + s44 + u10 + u43 + u44) + 1 ≤ (n + 1))
    (hcut39 : (s11 + s14 + s31 + u11 + u14 + u31 + 2) + 1 ≤ (n))
    (hcut55 : (s02 + s13 + s14 + s32 + s33 + u02 + u13 + u14 + u32 + u33) + 1 ≤ (n))
    (hcut28 : (s13 + s14 + s43 + u13 + u14 + u43 + 1) + 1 ≤ (n))
    (hcut44 : (s03 + s11 + s30 + u03 + u11 + u30 + 1) + 1 ≤ (n))
    (hcut57 : (s02 + s13 + s30 + s33 + u02 + u13 + u30 + u33 + 1) + 1 ≤ (n))
    (hcut31 : (s13 + s31 + u13 + u31 + 3) + 1 ≤ (n))
    (hcut1 : (s02 + s10 + s13 + s14 + s32 + s43 + u02 + u10 + u13 + u14 + u32 + u43) + 1 ≤ (n + 1))
    (hcut32 : (s10 + s14 + u10 + u14 + 2) + 1 ≤ (n))
    (hcut25 : (s03 + s04 + s12 + u03 + u04 + u12) + 1 ≤ (n))
    (hcut4 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 2))
    (hcut13 : (s12 + s41 + u12 + u41 + 2) + 1 ≤ (n))
    (hcut52 : (s02 + s13 + s33 + s41 + u02 + u13 + u33 + u41 + 1) + 1 ≤ (n))
    (hcut49 : (s01 + s02 + s14 + s32 + u01 + u02 + u14 + u32 + 1) + 1 ≤ (n))
    (hcut34 : (s11 + s13 + u11 + u13 + 2) + 1 ≤ (n))
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
    (hcase120a : s12 = 0)
    (hcase120b : u12 = 0)
    : False := by
  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
  ·
    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
    ·
      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
      ·
        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase110b hcase100b hcase140b hcase00 hcase01 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase110b hcase100a hcase100b hcase141a hcase00 hcase01 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase110b hcase101a hcase00 hcase01 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase140a hcase140b hcase320b hcase00 hcase01 hcase10 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase140a hcase140b hcase321a hcase321b hcase330a hcase330b hcase340b hcase00 hcase01 hcase10 hcase12 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                          ·
                            clear hn4 hsum_nat1 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase020a hcase020b hcase030b hcase040b hcase130a hcase130b hcase140a hcase140b hcase321a hcase321b hcase330a hcase330b hcase341a hcase341b hcase400b hcase410b hcase430b hcase010b hcase00 hcase10 hcase12 hcase30 hcase31 hcase42 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut62 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase020a hcase020b hcase030b hcase040b hcase130a hcase130b hcase140a hcase140b hcase321a hcase321b hcase330a hcase330b hcase341a hcase341b hcase400b hcase410b hcase430b hcase011a hcase00 hcase10 hcase12 hcase30 hcase31 hcase42 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase140a hcase140b hcase321a hcase330a hcase330b hcase341a hcase341b hcase400b hcase410b hcase431a hcase00 hcase01 hcase10 hcase12 hcase30 hcase31 hcase42 hcase44
                          omega
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase140a hcase140b hcase321a hcase321b hcase330a hcase330b hcase341a hcase400a hcase400b hcase411a hcase411b hcase430a hcase430b hcase440b hcase00 hcase01 hcase10 hcase12 hcase30 hcase31 hcase42
                            omega
                          ·
                            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase020b hcase030b hcase040b hcase130a hcase130b hcase111a hcase111b hcase140a hcase140b hcase321a hcase321b hcase330a hcase330b hcase341a hcase341b hcase400b hcase411a hcase430b hcase441a hcase010b hcase00 hcase10 hcase12 hcase30 hcase31 hcase42
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase140a hcase140b hcase321a hcase321b hcase330b hcase341a hcase341b hcase400a hcase400b hcase411a hcase411b hcase430a hcase430b hcase441a hcase441b hcase00 hcase10 hcase12 hcase30 hcase31 hcase42
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase140a hcase140b hcase321a hcase321b hcase330a hcase330b hcase341a hcase341b hcase400a hcase400b hcase411a hcase431a hcase00 hcase01 hcase10 hcase12 hcase30 hcase31 hcase42 hcase44
                          omega
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase111a hcase140b hcase321a hcase321b hcase330a hcase330b hcase341b hcase401a hcase401b hcase100b hcase00 hcase01 hcase12 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase140a hcase140b hcase321a hcase321b hcase330a hcase330b hcase401a hcase401b hcase101a hcase101b hcase430a hcase430b hcase440b hcase00 hcase01 hcase12 hcase30 hcase31 hcase41 hcase42
                            omega
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase111a hcase140b hcase321a hcase330a hcase330b hcase401a hcase101a hcase430b hcase441a hcase410b hcase00 hcase01 hcase12 hcase30 hcase31 hcase42
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase140a hcase140b hcase321a hcase321b hcase330a hcase330b hcase341a hcase341b hcase401a hcase101a hcase101b hcase430a hcase430b hcase441a hcase441b hcase411a hcase00 hcase01 hcase12 hcase30 hcase31 hcase42
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase140a hcase140b hcase321a hcase321b hcase330a hcase330b hcase341a hcase341b hcase401a hcase101a hcase101b hcase431a hcase00 hcase01 hcase12 hcase30 hcase31 hcase41 hcase42 hcase44
                          omega
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase111a hcase140b hcase321a hcase321b hcase331b hcase100b hcase00 hcase01 hcase12 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase111a hcase140b hcase321a hcase321b hcase101a hcase00 hcase01 hcase12 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase111a hcase141a hcase100b hcase00 hcase01 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase141a hcase141b hcase101a hcase101b hcase410a hcase410b hcase340b hcase00 hcase01 hcase12 hcase30 hcase31 hcase32 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase111a hcase141a hcase101a hcase410b hcase341a hcase341b hcase330a hcase330b hcase010a hcase010b hcase400b hcase00 hcase12 hcase30 hcase31 hcase32 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase111a hcase141a hcase101a hcase410a hcase410b hcase341a hcase341b hcase330a hcase330b hcase010a hcase010b hcase401a hcase401b hcase320b hcase00 hcase12 hcase30 hcase31 hcase42 hcase43 hcase44
                            omega
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase141a hcase101a hcase410b hcase330a hcase330b hcase010a hcase010b hcase401a hcase321a hcase440b hcase00 hcase12 hcase30 hcase31 hcase42 hcase43
                              omega
                            ·
                              clear hn4 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase130a hcase130b hcase111a hcase141a hcase101a hcase410b hcase330a hcase330b hcase010b hcase401a hcase321a hcase441a hcase00 hcase12 hcase30 hcase31 hcase42 hcase43
                              omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase141a hcase141b hcase101a hcase101b hcase410a hcase410b hcase341a hcase341b hcase330b hcase00 hcase12 hcase30 hcase31 hcase32 hcase40 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase111a hcase141a hcase101a hcase410a hcase410b hcase341a hcase341b hcase331a hcase331b hcase010a hcase010b hcase300a hcase300b hcase320b hcase00 hcase12 hcase31 hcase40 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase130a hcase130b hcase111a hcase101a hcase410b hcase341a hcase331a hcase010b hcase300b hcase321a hcase00 hcase12 hcase31 hcase40 hcase42 hcase43 hcase44
                            omega
                        ·
                          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase111a hcase141a hcase101a hcase410a hcase410b hcase341a hcase341b hcase331a hcase331b hcase010a hcase010b hcase301a hcase301b hcase320b hcase00 hcase12 hcase31 hcase40 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase141a hcase141b hcase101a hcase101b hcase410a hcase410b hcase341a hcase331a hcase010a hcase010b hcase301a hcase321a hcase00 hcase12 hcase31 hcase40 hcase42 hcase43 hcase44
                            omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase141a hcase101a hcase410b hcase011a hcase011b hcase440b hcase00 hcase12 hcase30 hcase31 hcase32 hcase40 hcase42 hcase43
                          omega
                        ·
                          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase111a hcase141a hcase101a hcase410a hcase410b hcase341a hcase341b hcase331a hcase331b hcase011a hcase011b hcase441a hcase441b hcase320b hcase00 hcase12 hcase30 hcase31 hcase40 hcase42 hcase43
                            omega
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase111a hcase141a hcase410b hcase341a hcase341b hcase331a hcase331b hcase011a hcase011b hcase441a hcase321a hcase400b hcase00 hcase12 hcase30 hcase31 hcase42 hcase43
                              omega
                            ·
                              clear hn4 hsum_nat3 hcut62 hcut2 hcut64 hcut58 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase130a hcase130b hcase111a hcase141a hcase101a hcase410b hcase331a hcase011a hcase441a hcase321a hcase401a hcase00 hcase12 hcase30 hcase31 hcase42 hcase43
                              omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase111a hcase141a hcase101a hcase411a hcase411b hcase300a hcase300b hcase320b hcase00 hcase01 hcase12 hcase31 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase141a hcase141b hcase101a hcase101b hcase411a hcase411b hcase300a hcase300b hcase321a hcase321b hcase400a hcase400b hcase340b hcase00 hcase01 hcase12 hcase31 hcase33 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                          ·
                            clear hn4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut21 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase130a hcase130b hcase111a hcase101a hcase411a hcase300b hcase321a hcase400b hcase341a hcase010b hcase00 hcase12 hcase31 hcase33 hcase42 hcase43 hcase44
                            omega
                          ·
                            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                            ·
                              clear hn4 hsum_nat3 hcut62 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase130a hcase130b hcase111a hcase101a hcase411a hcase300a hcase300b hcase321a hcase400b hcase341a hcase341b hcase310b hcase00 hcase12 hcase33 hcase42 hcase43 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat3 hcut62 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase130a hcase130b hcase111a hcase101a hcase411a hcase300a hcase300b hcase321a hcase400b hcase341a hcase341b hcase011a hcase311a hcase00 hcase12 hcase33 hcase42 hcase43 hcase44
                              omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase141a hcase141b hcase101a hcase101b hcase411a hcase300a hcase300b hcase321a hcase321b hcase401a hcase00 hcase01 hcase12 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase141a hcase141b hcase101a hcase101b hcase411a hcase411b hcase301a hcase301b hcase340b hcase00 hcase01 hcase12 hcase31 hcase32 hcase33 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase141a hcase141b hcase101a hcase101b hcase411a hcase411b hcase301a hcase301b hcase440b hcase00 hcase01 hcase12 hcase31 hcase32 hcase33 hcase40 hcase42 hcase43
                        omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                          ·
                            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase111a hcase141a hcase101a hcase411a hcase411b hcase301a hcase301b hcase341a hcase341b hcase441a hcase441b hcase400a hcase400b hcase010a hcase010b hcase320b hcase00 hcase12 hcase31 hcase33 hcase42 hcase43
                              omega
                            ·
                              clear hn4 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase130a hcase130b hcase111a hcase101a hcase411a hcase301a hcase301b hcase341a hcase341b hcase441a hcase400b hcase010b hcase321a hcase00 hcase12 hcase31 hcase33 hcase42 hcase43
                              omega
                          ·
                            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130b hcase111a hcase141a hcase101a hcase411a hcase411b hcase301a hcase301b hcase341a hcase341b hcase441a hcase441b hcase400a hcase400b hcase011a hcase011b hcase320b hcase00 hcase12 hcase31 hcase33 hcase42 hcase43
                              omega
                            ·
                              clear hn4 hcut62 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase130a hcase130b hcase111a hcase141a hcase101a hcase411a hcase301b hcase341b hcase441a hcase400b hcase321a hcase00 hcase12 hcase31 hcase33 hcase42 hcase43
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase130a hcase130b hcase111a hcase111b hcase141a hcase141b hcase101a hcase101b hcase411a hcase301a hcase301b hcase341a hcase341b hcase441a hcase441b hcase401a hcase00 hcase01 hcase12 hcase31 hcase32 hcase33 hcase42 hcase43
                          omega
        ·
          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300a hcase300b hcase310a hcase310b hcase320a hcase320b hcase110b hcase140b hcase100b hcase00 hcase12 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hsum_nat0 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300b hcase310b hcase320b hcase110b hcase140a hcase140b hcase101a hcase340b hcase00 hcase12 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat4 hcut62 hcut53 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase010b hcase300b hcase310a hcase310b hcase320b hcase110b hcase140a hcase140b hcase101a hcase341a hcase00 hcase12 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300a hcase300b hcase310a hcase310b hcase320a hcase320b hcase110b hcase141a hcase100b hcase00 hcase12 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300a hcase300b hcase310a hcase310b hcase320a hcase320b hcase110b hcase141a hcase101a hcase00 hcase12 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase010a hcase010b hcase300a hcase300b hcase310a hcase310b hcase320b hcase00 hcase10 hcase12 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300a hcase300b hcase310a hcase310b hcase110b hcase100b hcase00 hcase12 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300a hcase300b hcase310a hcase310b hcase110b hcase101a hcase00 hcase12 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase010a hcase010b hcase300a hcase300b hcase310a hcase310b hcase321a hcase321b hcase111a hcase111b hcase140a hcase140b hcase340b hcase00 hcase10 hcase12 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300a hcase300b hcase310a hcase310b hcase321a hcase321b hcase111a hcase140b hcase341a hcase341b hcase100b hcase00 hcase12 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                          ·
                            clear hn4 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase010b hcase300b hcase310b hcase321a hcase111a hcase140a hcase140b hcase341a hcase101a hcase330b hcase00 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                            omega
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase010b hcase300a hcase300b hcase310b hcase321a hcase111a hcase140a hcase140b hcase341a hcase341b hcase101a hcase400b hcase00 hcase12 hcase41 hcase42 hcase43 hcase44
                              omega
                            ·
                              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                              ·
                                clear hn4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase010b hcase300b hcase310b hcase321a hcase111a hcase140a hcase140b hcase341a hcase101a hcase331a hcase401a hcase410b hcase00 hcase12 hcase42 hcase43 hcase44
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase010a hcase010b hcase300a hcase300b hcase310a hcase310b hcase321a hcase321b hcase111a hcase111b hcase140a hcase140b hcase341a hcase341b hcase101a hcase101b hcase331a hcase331b hcase401a hcase411a hcase00 hcase12 hcase42 hcase43 hcase44
                                omega
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300a hcase300b hcase310a hcase310b hcase321a hcase321b hcase111a hcase141a hcase100b hcase00 hcase12 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300a hcase300b hcase310a hcase310b hcase321a hcase321b hcase111a hcase141a hcase101a hcase00 hcase12 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300a hcase300b hcase110a hcase110b hcase100b hcase00 hcase12 hcase14 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat4 hcut62 hcut53 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase010b hcase300b hcase311a hcase110b hcase101a hcase320b hcase00 hcase12 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300a hcase300b hcase311a hcase311b hcase110b hcase101a hcase00 hcase12 hcase14 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase010a hcase010b hcase300b hcase311a hcase111a hcase111b hcase330b hcase440b hcase320b hcase00 hcase10 hcase12 hcase14 hcase34 hcase40 hcase41 hcase42 hcase43
                        omega
                      ·
                        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300a hcase300b hcase111a hcase330a hcase330b hcase440a hcase440b hcase321a hcase321b hcase100b hcase00 hcase12 hcase14 hcase34 hcase40 hcase41 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase010a hcase010b hcase300b hcase311a hcase111a hcase330a hcase330b hcase440b hcase321a hcase101a hcase00 hcase12 hcase14 hcase34 hcase40 hcase41 hcase42 hcase43
                          omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase010a hcase010b hcase300a hcase300b hcase311a hcase311b hcase111a hcase111b hcase330a hcase330b hcase441a hcase441b hcase340b hcase00 hcase10 hcase12 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43
                        omega
                      ·
                        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300a hcase300b hcase111a hcase330a hcase330b hcase441a hcase441b hcase341a hcase341b hcase100b hcase00 hcase12 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43
                          omega
                        ·
                          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase010a hcase010b hcase300a hcase300b hcase311a hcase311b hcase330a hcase330b hcase441a hcase441b hcase341a hcase341b hcase101a hcase101b hcase320b hcase00 hcase12 hcase14 hcase40 hcase41 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat4 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase010b hcase300b hcase311a hcase111a hcase330a hcase330b hcase441a hcase341a hcase101a hcase321a hcase00 hcase12 hcase14 hcase40 hcase41 hcase42 hcase43
                            omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300a hcase300b hcase111a hcase100b hcase00 hcase12 hcase14 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat4 hcut53 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase010b hcase300b hcase311a hcase111a hcase101a hcase320b hcase00 hcase12 hcase14 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase300b hcase311a hcase111a hcase331a hcase101a hcase321a hcase340b hcase00 hcase12 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase010a hcase010b hcase300a hcase300b hcase311a hcase111a hcase111b hcase331a hcase101a hcase101b hcase321a hcase341a hcase00 hcase12 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase010a hcase010b hcase400a hcase400b hcase100b hcase00 hcase11 hcase12 hcase14 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut39 hcut55 hcut44 hcut57 hcut1 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020b hcase030b hcase040b hcase010b hcase301a hcase301b hcase400b hcase101a hcase110b hcase410b hcase00 hcase12 hcase14 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut13 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase010b hcase301a hcase301b hcase400b hcase101a hcase101b hcase110a hcase110b hcase411a hcase430b hcase00 hcase12 hcase14 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase010a hcase010b hcase301a hcase301b hcase400a hcase400b hcase101a hcase101b hcase110a hcase110b hcase411a hcase431a hcase00 hcase12 hcase14 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                        omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase020a hcase020b hcase030b hcase040b hcase010b hcase301a hcase301b hcase400b hcase410b hcase00 hcase12 hcase14 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase010a hcase010b hcase301a hcase301b hcase400a hcase400b hcase101a hcase101b hcase411a hcase411b hcase320b hcase00 hcase12 hcase14 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase010b hcase301a hcase301b hcase400b hcase101a hcase111a hcase411a hcase321a hcase00 hcase12 hcase14 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                        omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase010a hcase010b hcase401a hcase401b hcase320a hcase320b hcase100b hcase00 hcase11 hcase12 hcase14 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase010a hcase010b hcase301a hcase401a hcase401b hcase320b hcase101a hcase101b hcase440b hcase310b hcase00 hcase11 hcase12 hcase14 hcase33 hcase34 hcase41 hcase42 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut62 hcut53 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase010a hcase010b hcase301a hcase401a hcase401b hcase320b hcase101a hcase440b hcase311a hcase00 hcase11 hcase12 hcase14 hcase33 hcase34 hcase41 hcase42 hcase43
                        omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase010a hcase010b hcase301a hcase401a hcase401b hcase320b hcase101a hcase441a hcase441b hcase340b hcase00 hcase11 hcase12 hcase14 hcase31 hcase33 hcase41 hcase42 hcase43
                        omega
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut31 hcut1 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase020a hcase020b hcase030b hcase040b hcase010b hcase301a hcase401a hcase401b hcase320b hcase101a hcase101b hcase441a hcase341a hcase310b hcase00 hcase11 hcase12 hcase14 hcase33 hcase41 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat4 hcut62 hcut53 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase020a hcase020b hcase030b hcase040b hcase010b hcase301a hcase401a hcase401b hcase320b hcase101a hcase441a hcase341a hcase311a hcase00 hcase11 hcase12 hcase14 hcase33 hcase41 hcase42 hcase43
                          omega
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase010a hcase010b hcase301a hcase301b hcase401a hcase401b hcase321a hcase321b hcase340b hcase00 hcase10 hcase11 hcase12 hcase14 hcase31 hcase33 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase010a hcase010b hcase401a hcase401b hcase321a hcase321b hcase341a hcase341b hcase100b hcase00 hcase11 hcase12 hcase14 hcase31 hcase33 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase010a hcase010b hcase301a hcase301b hcase401a hcase401b hcase341a hcase341b hcase101a hcase110b hcase00 hcase12 hcase14 hcase31 hcase33 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase010a hcase010b hcase301a hcase301b hcase401a hcase401b hcase321a hcase321b hcase101a hcase101b hcase111a hcase111b hcase410a hcase410b hcase440b hcase00 hcase12 hcase14 hcase31 hcase33 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase131a hcase010b hcase301a hcase301b hcase401a hcase321a hcase101a hcase111a hcase410b hcase441a hcase00 hcase12 hcase14 hcase31 hcase33 hcase42 hcase43
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase010a hcase010b hcase301a hcase301b hcase401a hcase321a hcase321b hcase341a hcase341b hcase101a hcase101b hcase111a hcase111b hcase411a hcase00 hcase12 hcase14 hcase31 hcase33 hcase42 hcase43 hcase44
                          omega
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase011a hcase011b hcase410a hcase410b hcase140a hcase140b hcase340b hcase00 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase40 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase011a hcase011b hcase410a hcase410b hcase140b hcase341a hcase341b hcase320a hcase320b hcase110b hcase100b hcase00 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut2 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase410a hcase410b hcase140a hcase140b hcase341a hcase341b hcase320a hcase320b hcase110b hcase101a hcase00 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase011a hcase011b hcase410a hcase410b hcase140a hcase140b hcase341a hcase341b hcase320b hcase00 hcase10 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase011a hcase011b hcase410a hcase410b hcase140b hcase341a hcase341b hcase321a hcase321b hcase110b hcase100b hcase00 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut2 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase410a hcase410b hcase140a hcase140b hcase341a hcase341b hcase321a hcase321b hcase110b hcase101a hcase00 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase410a hcase410b hcase140a hcase140b hcase341a hcase341b hcase321a hcase321b hcase111a hcase111b hcase330b hcase00 hcase10 hcase12 hcase30 hcase31 hcase40 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase011a hcase011b hcase410a hcase410b hcase140b hcase341a hcase341b hcase321a hcase321b hcase111a hcase331a hcase331b hcase100b hcase00 hcase12 hcase30 hcase31 hcase40 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut2 hcut64 hcut41 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase410b hcase140a hcase140b hcase341a hcase341b hcase321a hcase111a hcase331a hcase101a hcase400b hcase00 hcase12 hcase30 hcase31 hcase42 hcase43 hcase44
                            omega
                          ·
                            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                            ·
                              clear hn4 hcut2 hcut64 hcut58 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase040b hcase011a hcase410b hcase140a hcase140b hcase341a hcase321a hcase111a hcase331a hcase101a hcase401a hcase300b hcase00 hcase12 hcase31 hcase42 hcase43 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase011a hcase011b hcase410a hcase410b hcase140a hcase140b hcase341a hcase321a hcase111a hcase111b hcase331a hcase101a hcase101b hcase401a hcase401b hcase301a hcase00 hcase12 hcase31 hcase42 hcase43 hcase44
                              omega
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase410a hcase410b hcase141a hcase100b hcase00 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut2 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase410a hcase410b hcase141a hcase101a hcase110b hcase00 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase011a hcase011b hcase410a hcase410b hcase141a hcase101a hcase111a hcase00 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                    omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase411a hcase411b hcase320a hcase320b hcase100b hcase110b hcase140b hcase00 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase411a hcase411b hcase320a hcase320b hcase100b hcase110a hcase110b hcase141a hcase00 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase411a hcase411b hcase320a hcase320b hcase100b hcase111a hcase00 hcase12 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut2 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase411a hcase411b hcase320a hcase320b hcase101a hcase110b hcase00 hcase12 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase011a hcase011b hcase411a hcase411b hcase320b hcase101a hcase101b hcase00 hcase12 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase411a hcase411b hcase321a hcase321b hcase140a hcase140b hcase330b hcase00 hcase10 hcase11 hcase12 hcase30 hcase31 hcase34 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase411a hcase411b hcase321a hcase321b hcase140a hcase140b hcase331a hcase100b hcase00 hcase11 hcase12 hcase30 hcase31 hcase34 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut2 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase411a hcase411b hcase321a hcase321b hcase140a hcase140b hcase331a hcase101a hcase110b hcase00 hcase12 hcase30 hcase31 hcase34 hcase40 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut2 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase411a hcase321a hcase140b hcase331a hcase101a hcase111a hcase400b hcase00 hcase12 hcase30 hcase31 hcase34 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase131b hcase011a hcase011b hcase411a hcase321a hcase321b hcase140a hcase140b hcase331a hcase331b hcase101a hcase101b hcase111a hcase111b hcase401a hcase00 hcase12 hcase30 hcase31 hcase34 hcase42 hcase43 hcase44
                          omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase011a hcase011b hcase411a hcase411b hcase141a hcase110b hcase00 hcase10 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase011a hcase011b hcase411a hcase411b hcase321a hcase321b hcase141a hcase111a hcase100b hcase00 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase131a hcase011a hcase011b hcase411a hcase411b hcase321a hcase321b hcase141a hcase111a hcase101a hcase00 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                      omega
      ·
        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041b hcase100b hcase110b hcase130b hcase140b hcase00 hcase01 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase100b hcase110a hcase110b hcase130b hcase141a hcase00 hcase01 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase100b hcase110b hcase131a hcase140b hcase00 hcase01 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase100b hcase110b hcase131a hcase141a hcase00 hcase01 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase100b hcase111a hcase140b hcase00 hcase01 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase100b hcase111a hcase141a hcase130b hcase00 hcase01 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase100b hcase111a hcase141a hcase131a hcase00 hcase01 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase101a hcase140b hcase130b hcase110b hcase00 hcase01 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase101a hcase140b hcase130b hcase111a hcase00 hcase01 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut41 hcut6 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase101a hcase140b hcase131a hcase110b hcase010a hcase010b hcase300b hcase340b hcase00 hcase12 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut64 hcut41 hcut6 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase101a hcase140b hcase131a hcase110b hcase010a hcase010b hcase300b hcase341a hcase440b hcase00 hcase12 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat4 hcut62 hcut53 hcut64 hcut41 hcut6 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase041a hcase101a hcase140b hcase131a hcase110b hcase010b hcase300b hcase341a hcase441a hcase00 hcase12 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43
                        omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase101a hcase140b hcase131a hcase110b hcase010a hcase010b hcase301a hcase320a hcase320b hcase440b hcase310b hcase00 hcase12 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut64 hcut41 hcut6 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase101a hcase140a hcase140b hcase131a hcase110b hcase010a hcase010b hcase301a hcase320a hcase320b hcase440b hcase311a hcase00 hcase12 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43
                          omega
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut41 hcut6 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase101a hcase140a hcase140b hcase131a hcase110b hcase010a hcase010b hcase301a hcase320a hcase320b hcase441a hcase441b hcase340b hcase00 hcase12 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43
                          omega
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase140b hcase131a hcase110b hcase010a hcase010b hcase301a hcase301b hcase320a hcase320b hcase441a hcase341a hcase341b hcase310a hcase310b hcase400b hcase410b hcase00 hcase12 hcase33 hcase42 hcase43
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase140b hcase131a hcase110b hcase010a hcase010b hcase301a hcase301b hcase320a hcase320b hcase441a hcase341a hcase341b hcase310a hcase310b hcase400b hcase411a hcase00 hcase12 hcase33 hcase42 hcase43
                                omega
                            ·
                              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                              ·
                                clear hn4 hsum_nat0 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut39 hcut55 hcut28 hcut44 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase140b hcase131a hcase110b hcase010a hcase010b hcase301a hcase320b hcase441a hcase341a hcase310b hcase401a hcase410b hcase00 hcase12 hcase33 hcase42 hcase43
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase110a hcase110b hcase010a hcase010b hcase301a hcase301b hcase320a hcase320b hcase441a hcase441b hcase341a hcase341b hcase310a hcase310b hcase401a hcase411a hcase00 hcase12 hcase33 hcase42 hcase43
                                omega
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase140b hcase131a hcase110b hcase010a hcase010b hcase301a hcase301b hcase320a hcase320b hcase441a hcase341a hcase341b hcase410b hcase400b hcase00 hcase12 hcase33 hcase42 hcase43
                                omega
                              ·
                                clear hn4 hsum_nat0 hcut62 hcut53 hcut2 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut47 hcut5 hcut50 hcut8 hcut19 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase140a hcase140b hcase131a hcase110b hcase010a hcase010b hcase301a hcase320b hcase441a hcase341a hcase311a hcase410b hcase401a hcase00 hcase12 hcase33 hcase42 hcase43
                                omega
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase140b hcase131a hcase110b hcase010a hcase010b hcase301a hcase301b hcase320a hcase320b hcase441a hcase341a hcase341b hcase311a hcase411a hcase400b hcase00 hcase12 hcase33 hcase42 hcase43
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase110a hcase110b hcase010a hcase010b hcase301a hcase301b hcase320a hcase320b hcase441a hcase441b hcase341a hcase341b hcase311a hcase311b hcase411a hcase401a hcase00 hcase12 hcase33 hcase42 hcase43
                                omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase140a hcase140b hcase131a hcase110b hcase010a hcase010b hcase301a hcase301b hcase00 hcase12 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase110a hcase110b hcase011a hcase00 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase111a hcase111b hcase330a hcase330b hcase010a hcase010b hcase340b hcase00 hcase12 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase330a hcase330b hcase010a hcase010b hcase341a hcase341b hcase300a hcase300b hcase310a hcase310b hcase320b hcase00 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut13 hcut52 hcut49 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase041a hcase101a hcase140b hcase131a hcase111a hcase330b hcase010b hcase341a hcase300b hcase310b hcase321a hcase00 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                            omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase111a hcase111b hcase330a hcase330b hcase010a hcase010b hcase300a hcase300b hcase311a hcase311b hcase440b hcase00 hcase12 hcase32 hcase40 hcase41 hcase42 hcase43
                            omega
                          ·
                            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase330a hcase330b hcase010a hcase010b hcase341a hcase341b hcase300a hcase300b hcase311a hcase311b hcase441a hcase441b hcase320b hcase00 hcase12 hcase40 hcase41 hcase42 hcase43
                              omega
                            ·
                              clear hn4 hsum_nat4 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase041a hcase101a hcase140a hcase140b hcase131a hcase111a hcase330a hcase330b hcase010b hcase341a hcase300b hcase311a hcase441a hcase321a hcase00 hcase12 hcase40 hcase41 hcase42 hcase43
                              omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase041a hcase101a hcase140b hcase131a hcase330a hcase330b hcase010b hcase341a hcase341b hcase301a hcase301b hcase400b hcase410b hcase00 hcase12 hcase31 hcase32 hcase42 hcase43 hcase44
                            omega
                          ·
                            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase330a hcase330b hcase010a hcase010b hcase341a hcase341b hcase301a hcase301b hcase400a hcase400b hcase411a hcase411b hcase320b hcase00 hcase12 hcase31 hcase42 hcase43 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase041a hcase101a hcase140b hcase131a hcase111a hcase330a hcase330b hcase010b hcase341a hcase341b hcase301a hcase301b hcase400b hcase411a hcase321a hcase00 hcase12 hcase31 hcase42 hcase43 hcase44
                              omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase111a hcase111b hcase330a hcase330b hcase010a hcase010b hcase301a hcase301b hcase401a hcase401b hcase440b hcase00 hcase12 hcase31 hcase32 hcase41 hcase42 hcase43
                            omega
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase330a hcase330b hcase010a hcase010b hcase341a hcase341b hcase301a hcase301b hcase401a hcase401b hcase441a hcase441b hcase410a hcase410b hcase320b hcase00 hcase12 hcase31 hcase42 hcase43
                                omega
                              ·
                                clear hn4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut63 hcut66 hcut47 hcut5 hcut50 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase041a hcase101a hcase140a hcase140b hcase131a hcase111a hcase330b hcase010b hcase341a hcase301a hcase401a hcase441a hcase410b hcase321a hcase00 hcase12 hcase31 hcase42 hcase43
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase111a hcase111b hcase330a hcase330b hcase010a hcase010b hcase341a hcase341b hcase301a hcase301b hcase401a hcase441a hcase441b hcase411a hcase00 hcase12 hcase31 hcase32 hcase42 hcase43
                              omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase111a hcase111b hcase330a hcase330b hcase011a hcase00 hcase12 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase140a hcase140b hcase131a hcase111a hcase320b hcase00 hcase01 hcase12 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut5 hcut50 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase101a hcase140a hcase140b hcase131a hcase111a hcase331a hcase321a hcase010a hcase010b hcase340b hcase00 hcase12 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          clear hn4 hsum_nat4 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase101a hcase140a hcase140b hcase131a hcase111a hcase321a hcase010b hcase341a hcase300b hcase00 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase111a hcase111b hcase331a hcase321a hcase010a hcase010b hcase341a hcase301a hcase00 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase111a hcase111b hcase331a hcase331b hcase321a hcase321b hcase011a hcase00 hcase12 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase141a hcase320a hcase320b hcase110b hcase130b hcase00 hcase01 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase141a hcase320a hcase320b hcase110b hcase131a hcase00 hcase01 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase141a hcase141b hcase320b hcase00 hcase01 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase141a hcase321a hcase321b hcase010a hcase010b hcase130b hcase110b hcase00 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase141a hcase141b hcase321a hcase321b hcase010a hcase010b hcase130a hcase130b hcase111a hcase111b hcase340b hcase00 hcase12 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          clear hn4 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase041a hcase101a hcase141a hcase321a hcase010b hcase130b hcase111a hcase341a hcase300b hcase330b hcase00 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase101a hcase141a hcase321a hcase010b hcase130b hcase111a hcase341a hcase300b hcase331a hcase00 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase141a hcase141b hcase321a hcase321b hcase010a hcase010b hcase130a hcase130b hcase111a hcase111b hcase301a hcase301b hcase330a hcase330b hcase440b hcase00 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43
                            omega
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase141a hcase321a hcase321b hcase010a hcase010b hcase130b hcase111a hcase341a hcase341b hcase301a hcase301b hcase330a hcase330b hcase441a hcase410b hcase400b hcase00 hcase12 hcase31 hcase42 hcase43
                                omega
                              ·
                                clear hn4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut63 hcut66 hcut47 hcut5 hcut50 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase041a hcase101a hcase141a hcase321a hcase010b hcase130a hcase130b hcase111a hcase341a hcase301a hcase330b hcase441a hcase410b hcase401a hcase00 hcase12 hcase31 hcase42 hcase43
                                omega
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase030b hcase041a hcase101a hcase141a hcase321a hcase010b hcase130b hcase111a hcase341a hcase341b hcase301a hcase301b hcase330a hcase330b hcase441a hcase411a hcase400b hcase00 hcase12 hcase31 hcase42 hcase43
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase141a hcase141b hcase321a hcase321b hcase010a hcase010b hcase130a hcase130b hcase111a hcase111b hcase341a hcase341b hcase301a hcase301b hcase330a hcase330b hcase441a hcase441b hcase411a hcase401a hcase00 hcase12 hcase31 hcase42 hcase43
                                omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase101b hcase141a hcase141b hcase321a hcase010a hcase010b hcase130a hcase130b hcase111a hcase111b hcase341a hcase301a hcase331a hcase00 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase141a hcase010a hcase010b hcase131a hcase110b hcase00 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase101a hcase141a hcase321a hcase321b hcase010a hcase010b hcase131a hcase111a hcase00 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase030a hcase030b hcase041a hcase101a hcase101b hcase141a hcase141b hcase321a hcase321b hcase011a hcase00 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
    ·
      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
      ·
        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase100b hcase110b hcase130b hcase140b hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase100b hcase110a hcase110b hcase130b hcase141a hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase100b hcase110b hcase131a hcase140b hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase100b hcase110b hcase131a hcase141a hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase320b hcase100a hcase100b hcase00 hcase01 hcase04 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase101a hcase110b hcase140a hcase140b hcase130b hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase101a hcase101b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase340b hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320b hcase101a hcase110b hcase140a hcase140b hcase341a hcase300b hcase440b hcase00 hcase01 hcase04 hcase12 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320b hcase101a hcase110b hcase140b hcase131a hcase341a hcase300b hcase441a hcase00 hcase01 hcase04 hcase12 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43
                      omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase101a hcase101b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase301a hcase301b hcase440b hcase00 hcase01 hcase04 hcase12 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43
                      omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase101a hcase110b hcase140b hcase131a hcase341a hcase341b hcase301a hcase301b hcase441a hcase310a hcase310b hcase410b hcase400b hcase00 hcase01 hcase04 hcase12 hcase33 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut39 hcut55 hcut28 hcut44 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320b hcase101a hcase110b hcase140b hcase131a hcase341a hcase301a hcase441a hcase310b hcase410b hcase401a hcase00 hcase01 hcase04 hcase12 hcase33 hcase42 hcase43
                            omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase101a hcase110b hcase140b hcase131a hcase341a hcase341b hcase301a hcase301b hcase441a hcase310a hcase310b hcase411a hcase400b hcase00 hcase01 hcase04 hcase12 hcase33 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase101a hcase101b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase341a hcase341b hcase301a hcase301b hcase441a hcase441b hcase310a hcase310b hcase411a hcase401a hcase00 hcase01 hcase04 hcase12 hcase33 hcase42 hcase43
                            omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut39 hcut55 hcut28 hcut44 hcut57 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase101a hcase110b hcase140b hcase131a hcase341a hcase341b hcase301a hcase301b hcase441a hcase400b hcase410b hcase00 hcase01 hcase04 hcase12 hcase33 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase101a hcase110b hcase140b hcase131a hcase341a hcase341b hcase301a hcase301b hcase441a hcase311a hcase311b hcase400b hcase411a hcase00 hcase01 hcase04 hcase12 hcase33 hcase42 hcase43
                            omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat0 hcut62 hcut53 hcut2 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut47 hcut5 hcut50 hcut8 hcut19 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320b hcase101a hcase110b hcase140a hcase140b hcase131a hcase341a hcase301a hcase441a hcase311a hcase401a hcase410b hcase00 hcase01 hcase04 hcase12 hcase33 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase101a hcase101b hcase110a hcase110b hcase140a hcase140b hcase131a hcase131b hcase341a hcase341b hcase301a hcase301b hcase441a hcase441b hcase311a hcase311b hcase401a hcase411a hcase00 hcase01 hcase04 hcase12 hcase33 hcase42 hcase43
                            omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase101a hcase110b hcase141a hcase130b hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase320a hcase320b hcase101a hcase110b hcase141a hcase131a hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase320b hcase101a hcase101b hcase00 hcase01 hcase04 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
      ·
        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase100b hcase130b hcase110b hcase00 hcase01 hcase04 hcase12 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase321b hcase100b hcase130b hcase111a hcase00 hcase01 hcase04 hcase12 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase100b hcase131a hcase110b hcase00 hcase01 hcase04 hcase12 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase321b hcase100b hcase131a hcase111a hcase140b hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase321b hcase100b hcase131a hcase111a hcase141a hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140b hcase110b hcase130b hcase00 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase110b hcase131a hcase00 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase321a hcase321b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140b hcase111a hcase300a hcase300b hcase400a hcase400b hcase440a hcase440b hcase130b hcase00 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase111a hcase300b hcase400b hcase440b hcase00 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43
                          omega
                      ·
                        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase321a hcase321b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140b hcase111a hcase300a hcase300b hcase400a hcase400b hcase441a hcase441b hcase130b hcase00 hcase12 hcase31 hcase33 hcase34 hcase41 hcase42 hcase43
                          omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase321b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140b hcase111a hcase300a hcase300b hcase400b hcase441a hcase131a hcase410b hcase00 hcase12 hcase31 hcase33 hcase34 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase101a hcase010a hcase010b hcase040a hcase040b hcase140b hcase111a hcase300a hcase300b hcase400b hcase441a hcase131a hcase411a hcase00 hcase12 hcase31 hcase33 hcase34 hcase42 hcase43
                            omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase321b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase111a hcase111b hcase300a hcase300b hcase401a hcase401b hcase410a hcase410b hcase340b hcase00 hcase12 hcase13 hcase31 hcase33 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase321a hcase321b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140b hcase111a hcase300a hcase300b hcase401a hcase401b hcase410a hcase410b hcase341a hcase341b hcase130b hcase00 hcase12 hcase31 hcase33 hcase42 hcase43 hcase44
                            omega
                          ·
                            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                            ·
                              clear hn4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase031a hcase321a hcase101a hcase010b hcase040a hcase040b hcase140b hcase111a hcase300b hcase401a hcase410b hcase341a hcase131a hcase310b hcase00 hcase12 hcase33 hcase42 hcase43 hcase44
                              omega
                            ·
                              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat3 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase111a hcase300a hcase300b hcase401a hcase410b hcase131a hcase311a hcase311b hcase440b hcase00 hcase12 hcase33 hcase42 hcase43
                                omega
                              ·
                                clear hn4 hsum_nat0 hcut53 hcut2 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase111a hcase300b hcase401a hcase410b hcase341a hcase131a hcase311a hcase441a hcase00 hcase12 hcase33 hcase42 hcase43
                                omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase321b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase111a hcase111b hcase300a hcase300b hcase401a hcase411a hcase00 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase321b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase111a hcase111b hcase301a hcase301b hcase340b hcase00 hcase12 hcase13 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase321a hcase321b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140b hcase111a hcase301a hcase301b hcase341a hcase341b hcase310a hcase310b hcase130b hcase00 hcase12 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase321b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase111a hcase111b hcase301a hcase301b hcase310a hcase310b hcase131a hcase131b hcase440b hcase00 hcase12 hcase33 hcase40 hcase41 hcase42 hcase43
                            omega
                          ·
                            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                            ·
                              clear hn4 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase031a hcase321a hcase101a hcase010b hcase040b hcase140a hcase140b hcase111a hcase301a hcase341a hcase310b hcase131a hcase441a hcase330b hcase00 hcase12 hcase40 hcase41 hcase42 hcase43
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase111a hcase111b hcase301a hcase341a hcase310a hcase310b hcase131a hcase131b hcase441a hcase441b hcase331a hcase00 hcase12 hcase40 hcase41 hcase42 hcase43
                              omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase111a hcase111b hcase301a hcase341a hcase311a hcase00 hcase12 hcase13 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase130a hcase130b hcase110b hcase00 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase321a hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase130b hcase111a hcase440b hcase300b hcase00 hcase12 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43
                        omega
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase321a hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase130a hcase130b hcase111a hcase440b hcase301a hcase310b hcase330b hcase00 hcase12 hcase34 hcase40 hcase41 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut5 hcut50 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase321a hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase130a hcase130b hcase111a hcase440b hcase301a hcase310a hcase310b hcase331a hcase00 hcase12 hcase34 hcase40 hcase41 hcase42 hcase43
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut5 hcut50 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase321a hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase130a hcase130b hcase111a hcase440b hcase301a hcase311a hcase00 hcase12 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43
                          omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase321b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase130a hcase130b hcase111a hcase111b hcase441a hcase441b hcase340b hcase00 hcase12 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43
                        omega
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          clear hn4 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase031a hcase321a hcase101a hcase010b hcase040a hcase040b hcase141a hcase130b hcase111a hcase441a hcase341a hcase300b hcase00 hcase12 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43
                          omega
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                            ·
                              clear hn4 hsum_nat4 hcut62 hcut53 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut57 hcut31 hcut32 hcut25 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120b hcase020a hcase020b hcase031a hcase321a hcase101a hcase010b hcase040b hcase141a hcase130a hcase130b hcase111a hcase441a hcase341a hcase301a hcase310b hcase330b hcase00 hcase12 hcase40 hcase41 hcase42 hcase43
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase130a hcase130b hcase111a hcase111b hcase441a hcase441b hcase341a hcase301a hcase310a hcase310b hcase331a hcase00 hcase12 hcase40 hcase41 hcase42 hcase43
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase130a hcase130b hcase111a hcase111b hcase441a hcase441b hcase341a hcase301a hcase311a hcase00 hcase12 hcase33 hcase40 hcase41 hcase42 hcase43
                            omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase020a hcase020b hcase031a hcase031b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase131a hcase110b hcase00 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase031b hcase321a hcase321b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase131a hcase111a hcase00 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase321a hcase321b hcase101a hcase101b hcase010a hcase010b hcase041a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase120a hcase120b hcase020a hcase020b hcase031a hcase321a hcase321b hcase101a hcase101b hcase011a hcase00 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
  ·
    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
    ·
      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
      ·
        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase110b hcase100b hcase130b hcase00 hcase01 hcase03 hcase04 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase110b hcase100a hcase100b hcase131a hcase00 hcase01 hcase03 hcase04 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase110b hcase101a hcase00 hcase01 hcase03 hcase04 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
    ·
      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
      ·
        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
        ·
          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase111a hcase130b hcase140b hcase100b hcase00 hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase111a hcase130b hcase140b hcase101a hcase00 hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
        ·
          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase111a hcase130a hcase130b hcase141a hcase100b hcase00 hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase111a hcase130a hcase130b hcase141a hcase101a hcase00 hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
      ·
        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut53 hcut2 hcut64 hcut58 hcut41 hcut6 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut1 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase111a hcase131a hcase100b hcase00 hcase01 hcase03 hcase04 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut62 hcut53 hcut2 hcut64 hcut58 hcut41 hcut7 hcut59 hcut63 hcut66 hcut16 hcut47 hcut5 hcut50 hcut3 hcut8 hcut19 hcut12 hcut21 hcut39 hcut55 hcut28 hcut44 hcut57 hcut31 hcut32 hcut25 hcut4 hcut13 hcut52 hcut49 hcut34 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase111a hcase131a hcase101a hcase00 hcase01 hcase03 hcase04 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega

#print axioms symbolic_v2_mask254_integer_shard001
end Jsp404.SixExactFloorKernel
