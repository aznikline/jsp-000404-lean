import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask515_integer_shard002 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut28 : (s02 + s31 + u02 + u31) + 1 ≤ (s12 + 2))
    (hcut3 : (s02 + s13 + s42 + u02 + u13 + u42) + 1 ≤ (s32 + 2))
    (hcut53 : (s04 + s10 + s11 + s13 + s40 + s44 + u04 + u10 + u11 + u13 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut51 : (s40 + s41 + s42 + s43 + u40 + u41 + u42 + u43) + 1 ≤ (n))
    (hcut21 : (s40 + s41 + u40 + u41 + 1) + 1 ≤ (n))
    (hcut6 : (s03 + s41 + u03 + u41) + 1 ≤ (s13 + 2))
    (hcut31 : (s10 + s11 + s14 + u10 + u11 + u14 + 1) + 1 ≤ (n))
    (hcut39 : (s13 + s44 + u13 + u44) + 1 ≤ (n))
    (hcut15 : (s04 + s10 + u04 + u10) + 1 ≤ (n))
    (hcut57 : (s13 + s14 + s30 + u13 + u14 + u30) + 1 ≤ (n))
    (hcut64 : (s33 + s34 + s40 + s41 + s42 + u33 + u34 + u40 + u41 + u42) + 1 ≤ (n + 1))
    (hcut37 : (s00 + s43 + s44 + u00 + u43 + u44) + 1 ≤ (n + 1))
    (hcut45 : (s34 + s40 + s41 + u34 + u40 + u41) + 1 ≤ (n))
    (hcut65 : (s03 + s12 + s30 + u03 + u12 + u30) + 1 ≤ (s40 + 3))
    (hcut33 : (s12 + s30 + s33 + s34 + u12 + u30 + u33 + u34) + 1 ≤ (n))
    (hcut48 : (s12 + s33 + s42 + u12 + u33 + u42 + 1) + 1 ≤ (n))
    (hcut26 : (s12 + s30 + s42 + u12 + u30 + u42 + 1) + 1 ≤ (n))
    (hcut29 : (s12 + s30 + s34 + u12 + u30 + u34 + 1) + 1 ≤ (n))
    (hcut38 : (s14 + u14 + 2) + 1 ≤ (n))
    (hcut0 : (s02 + s03 + s30 + s31 + s34 + s41 + s42 + s43 + u02 + u03 + u30 + u31 + u34 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut22 : (s03 + s04 + s11 + s12 + u03 + u04 + u11 + u12) + 1 ≤ (n))
    (hcut43 : (s32 + s43 + s44 + u32 + u43 + u44) + 1 ≤ (n + 1))
    (hcut40 : (s01 + s32 + u01 + u32 + 1) + 1 ≤ (n))
    (hcut62 : (s33 + s40 + s41 + s42 + u33 + u40 + u41 + u42) + 1 ≤ (n))
    (hcut59 : (s00 + s01 + s32 + s44 + u00 + u01 + u32 + u44) + 1 ≤ (n + 2))
    (hcut66 : (s00 + s01 + s04 + s32 + s40 + s43 + s44 + u00 + u01 + u04 + u32 + u40 + u43 + u44) + 1 ≤ (2 * n + 2))
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
    (hcase030a : s03 = 0)
    (hcase030b : u03 = 0)
    (hcase020a : s02 = 0)
    (hcase020b : u02 = 0)
    (hcase010a : s01 = 0)
    (hcase010b : u01 = 0)
    (hcase001a : 1 ≤ s00)
    (hcase001b : u00 = 1)
    (hcase101a : 1 ≤ s10)
    (hcase101b : u10 = 1)
    : False := by
  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
  ·
    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
    ·
      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
      ·
        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101b hcase040a hcase040b hcase330b hcase310b hcase300b hcase320b hcase340b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase101b hcase040b hcase330a hcase330b hcase310a hcase310b hcase300a hcase300b hcase320a hcase320b hcase341a hcase341b hcase410b hcase400b hcase420b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010b hcase001a hcase101b hcase040b hcase330a hcase330b hcase310a hcase310b hcase300a hcase300b hcase320b hcase341a hcase341b hcase410b hcase400b hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330b hcase310b hcase300b hcase320b hcase341a hcase410a hcase410b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020b hcase010b hcase001a hcase101b hcase040b hcase330a hcase330b hcase310b hcase300b hcase320b hcase341a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010a hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase310a hcase310b hcase300a hcase300b hcase340a hcase340b hcase430b hcase400b hcase410b hcase420b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase310a hcase310b hcase300a hcase300b hcase340a hcase340b hcase430b hcase400b hcase410b hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020b hcase010a hcase010b hcase001a hcase101b hcase040b hcase330b hcase310b hcase300b hcase321a hcase340b hcase430a hcase430b hcase400a hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase42 hcase44
                    omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hsum_nat1 hcut28 hcut3 hcut53 hcut51 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010a hcase010b hcase001a hcase101a hcase101b hcase040b hcase330b hcase310b hcase300b hcase321a hcase340b hcase430b hcase401a hcase420b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase41 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330a hcase330b hcase310a hcase310b hcase300a hcase300b hcase321a hcase321b hcase340a hcase340b hcase430a hcase430b hcase401a hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase41 hcase44
                    omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase310a hcase310b hcase300a hcase300b hcase321a hcase321b hcase340a hcase340b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase44
                omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase310a hcase310b hcase300a hcase300b hcase321b hcase341b hcase130a hcase130b hcase400b hcase410b hcase420b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase310a hcase310b hcase300a hcase300b hcase321a hcase321b hcase341b hcase130a hcase130b hcase400b hcase410b hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330a hcase330b hcase310a hcase310b hcase300a hcase300b hcase321a hcase321b hcase341a hcase341b hcase130b hcase400a hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase310a hcase310b hcase300a hcase300b hcase321a hcase321b hcase130a hcase130b hcase401a hcase420b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330a hcase330b hcase310a hcase310b hcase300a hcase300b hcase321a hcase321b hcase341a hcase341b hcase130a hcase130b hcase401a hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase43 hcase44
                    omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    clear hn4 hsum_nat1 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase310a hcase310b hcase300a hcase300b hcase321a hcase321b hcase341b hcase400b hcase410b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hcut28 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase310a hcase310b hcase300a hcase300b hcase321a hcase321b hcase341b hcase131a hcase400b hcase411a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase310a hcase310b hcase300a hcase300b hcase321a hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase41 hcase42 hcase43 hcase44
                  omega
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase310a hcase310b hcase400b hcase410b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase32 hcase34 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330a hcase330b hcase310a hcase310b hcase301a hcase301b hcase400a hcase400b hcase130b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase34 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hcut28 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase310a hcase310b hcase301b hcase400b hcase411a hcase131a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase34 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
            ·
              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330a hcase330b hcase310a hcase310b hcase301a hcase301b hcase401a hcase430b hcase440b hcase420b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase32 hcase34 hcase41
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330a hcase330b hcase310a hcase310b hcase301a hcase301b hcase401a hcase430a hcase430b hcase440a hcase440b hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase32 hcase34 hcase41
                  omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase310a hcase310b hcase301a hcase301b hcase401a hcase401b hcase430a hcase430b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase32 hcase34 hcase41 hcase42
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330a hcase330b hcase310a hcase310b hcase301a hcase301b hcase401a hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase32 hcase34 hcase41 hcase42 hcase44
              omega
      ·
        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
        ·
          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
          ·
            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330a hcase330b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase400a hcase400b hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase30 hcase32 hcase42 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase340a hcase340b hcase410b hcase430a hcase430b hcase400b hcase121a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase30 hcase32 hcase42 hcase44
                  omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101b hcase040a hcase040b hcase330b hcase311a hcase340b hcase410a hcase410b hcase430a hcase430b hcase401a hcase401b hcase320b hcase300b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase42 hcase44
                    omega
                  ·
                    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330a hcase330b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase401a hcase401b hcase320a hcase320b hcase301a hcase301b hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330b hcase311a hcase340b hcase410a hcase410b hcase430a hcase430b hcase401a hcase401b hcase320b hcase301a hcase121a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase42 hcase44
                      omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010a hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase311a hcase311b hcase340a hcase340b hcase410a hcase410b hcase430b hcase401a hcase420b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330a hcase330b hcase311a hcase311b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase401a hcase321a hcase321b hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase44
                    omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase311a hcase311b hcase340a hcase340b hcase410a hcase410b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase32 hcase40 hcase42 hcase44
              omega
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101b hcase040a hcase040b hcase330b hcase311a hcase340b hcase300b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase101b hcase040b hcase330b hcase311a hcase340b hcase300b hcase321a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330b hcase311a hcase340a hcase340b hcase301a hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hcut28 hcut3 hcut53 hcut51 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase101a hcase101b hcase040b hcase330b hcase311a hcase340a hcase340b hcase301a hcase321a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330a hcase330b hcase341a hcase341b hcase320a hcase320b hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330b hcase311a hcase341a hcase320b hcase121a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase330a hcase330b hcase311a hcase311b hcase321a hcase321b hcase401a hcase420b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase41 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase040a hcase040b hcase330a hcase330b hcase311a hcase311b hcase341a hcase341b hcase321a hcase321b hcase401a hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase41 hcase43 hcase44
                omega
    ·
      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
      ·
        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
        ·
          clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase400b hcase410b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
          omega
        ·
          clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase400a hcase400b hcase411a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
          omega
      ·
        clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase101a hcase101b hcase040b hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
        omega
  ·
    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
    ·
      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
      ·
        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase340b hcase410a hcase410b hcase430a hcase430b hcase320b hcase300b hcase330b hcase310b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase42 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101b hcase041a hcase041b hcase340b hcase410a hcase410b hcase430a hcase430b hcase320b hcase300b hcase330b hcase311a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase42 hcase44
                  omega
              ·
                rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320a hcase320b hcase300a hcase300b hcase331a hcase331b hcase120b hcase110b hcase140b hcase130b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase40 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320b hcase300a hcase300b hcase331a hcase331b hcase120b hcase110b hcase140b hcase131a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase40 hcase42 hcase44
                        omega
                    ·
                      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320a hcase320b hcase300a hcase300b hcase331a hcase331b hcase120b hcase110a hcase110b hcase141a hcase130b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase40 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320b hcase300a hcase300b hcase331a hcase331b hcase120b hcase110a hcase110b hcase141a hcase131a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase40 hcase42 hcase44
                        omega
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320a hcase320b hcase300a hcase300b hcase331a hcase331b hcase120b hcase111a hcase130b hcase00 hcase01 hcase02 hcase03 hcase10 hcase14 hcase31 hcase40 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320b hcase300a hcase300b hcase331a hcase331b hcase120a hcase120b hcase111a hcase111b hcase00 hcase01 hcase02 hcase03 hcase10 hcase14 hcase31 hcase40 hcase42 hcase44
                      omega
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320b hcase300a hcase300b hcase331a hcase310b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase40 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340b hcase410a hcase410b hcase430a hcase430b hcase320b hcase300b hcase331a hcase121a hcase311a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase40 hcase42 hcase44
                    omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320a hcase320b hcase301a hcase301b hcase130b hcase310a hcase310b hcase120b hcase140b hcase110b hcase00 hcase01 hcase02 hcase03 hcase10 hcase33 hcase40 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320a hcase320b hcase301a hcase301b hcase130b hcase310a hcase310b hcase120b hcase140a hcase140b hcase111a hcase00 hcase01 hcase02 hcase03 hcase10 hcase33 hcase40 hcase42 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320a hcase320b hcase301a hcase301b hcase130b hcase310a hcase310b hcase120b hcase141a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase33 hcase40 hcase42 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320b hcase301a hcase130a hcase130b hcase310b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase14 hcase33 hcase40 hcase42 hcase44
                    omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320a hcase320b hcase301a hcase301b hcase130a hcase130b hcase330a hcase330b hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase14 hcase40 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340b hcase410a hcase410b hcase430a hcase430b hcase320b hcase301a hcase130a hcase130b hcase311a hcase330b hcase121a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase14 hcase40 hcase42 hcase44
                      omega
                  ·
                    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320a hcase320b hcase301a hcase301b hcase130a hcase130b hcase331a hcase331b hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase14 hcase40 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320b hcase301a hcase130a hcase130b hcase311a hcase331a hcase121a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase14 hcase40 hcase42 hcase44
                      omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase320b hcase301a hcase301b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase33 hcase40 hcase42 hcase44
                omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                  ·
                    clear hn4 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase340a hcase340b hcase410b hcase430b hcase321a hcase400b hcase110b hcase140b hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase31 hcase33 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010a hcase010b hcase001a hcase041a hcase340a hcase340b hcase410b hcase430b hcase400b hcase110b hcase140b hcase121a hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase31 hcase33 hcase42 hcase44
                    omega
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                    ·
                      clear hn4 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut6 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase041a hcase340a hcase340b hcase410b hcase430b hcase321a hcase400b hcase110a hcase110b hcase141a hcase310a hcase310b hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase33 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut39 hcut57 hcut64 hcut37 hcut45 hcut33 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010a hcase010b hcase001a hcase041a hcase340b hcase410b hcase430b hcase321a hcase400b hcase110a hcase110b hcase141a hcase310b hcase121a hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase33 hcase42 hcase44
                      omega
                  ·
                    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                    ·
                      clear hn4 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut6 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase041a hcase340a hcase340b hcase410b hcase430b hcase321a hcase400b hcase110a hcase110b hcase141a hcase311a hcase311b hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase33 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hcut53 hcut51 hcut21 hcut6 hcut39 hcut57 hcut64 hcut37 hcut45 hcut33 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase041a hcase340b hcase410b hcase430b hcase321a hcase400b hcase110a hcase110b hcase141a hcase311a hcase121a hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase30 hcase33 hcase42 hcase44
                      omega
              ·
                clear hn4 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut6 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase101a hcase041a hcase340a hcase340b hcase410b hcase430b hcase321a hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase42 hcase44
                omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase430b hcase321a hcase321b hcase401a hcase420b hcase440b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010a hcase010b hcase001a hcase101a hcase101b hcase041a hcase340a hcase340b hcase410b hcase430a hcase430b hcase401a hcase420b hcase441a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase430a hcase430b hcase321a hcase321b hcase401a hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase44
                omega
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase041a hcase340a hcase340b hcase410b hcase431a hcase400b hcase420b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase431a hcase400a hcase400b hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase410a hcase410b hcase431a hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase42 hcase44
            omega
      ·
        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hsum_nat0 hsum_nat1 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340b hcase411a hcase411b hcase330b hcase300b hcase120a hcase120b hcase310b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase40 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020b hcase010a hcase010b hcase001a hcase041a hcase340b hcase411a hcase330b hcase300b hcase120a hcase120b hcase310b hcase321a hcase400b hcase420b hcase430b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase330a hcase330b hcase300a hcase300b hcase120a hcase120b hcase310a hcase310b hcase321a hcase321b hcase400a hcase400b hcase420a hcase420b hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase330a hcase330b hcase300a hcase300b hcase120a hcase120b hcase310a hcase310b hcase321a hcase321b hcase400a hcase400b hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase330a hcase330b hcase300a hcase300b hcase120a hcase120b hcase310a hcase310b hcase321a hcase321b hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase42 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase411b hcase330a hcase330b hcase300a hcase300b hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase32 hcase40 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101b hcase041a hcase041b hcase340b hcase330b hcase300b hcase121a hcase121b hcase420a hcase420b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase31 hcase40 hcase43 hcase44
                  omega
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat0 hcut28 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101b hcase041a hcase041b hcase340b hcase411a hcase330b hcase300b hcase121b hcase420b hcase321a hcase310b hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase330a hcase330b hcase300a hcase300b hcase121a hcase121b hcase420a hcase420b hcase321a hcase321b hcase310a hcase310b hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase43 hcase44
                      omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase041a hcase340b hcase411a hcase330b hcase300b hcase121a hcase121b hcase420b hcase321a hcase311a hcase430b hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase330a hcase330b hcase300a hcase300b hcase121a hcase121b hcase420a hcase420b hcase321a hcase321b hcase311a hcase311b hcase430a hcase430b hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase330a hcase330b hcase300a hcase300b hcase121a hcase121b hcase420a hcase420b hcase321a hcase321b hcase311a hcase311b hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase40 hcase44
                      omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase330a hcase330b hcase300a hcase300b hcase121a hcase121b hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase31 hcase32 hcase40 hcase43 hcase44
                omega
          ·
            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase330a hcase330b hcase440b hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase42 hcase43
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase330a hcase330b hcase301a hcase301b hcase440a hcase440b hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase42 hcase43
                omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase330a hcase330b hcase301a hcase301b hcase441a hcase441b hcase110a hcase110b hcase120a hcase120b hcase130b hcase00 hcase01 hcase02 hcase03 hcase10 hcase14 hcase31 hcase32 hcase40 hcase42 hcase43
                    omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase330a hcase330b hcase301a hcase301b hcase441a hcase441b hcase110a hcase110b hcase120a hcase120b hcase131a hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase14 hcase31 hcase40 hcase42 hcase43
                      omega
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        clear hn4 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase101a hcase041a hcase340a hcase340b hcase411a hcase411b hcase330a hcase330b hcase301a hcase301b hcase110b hcase120b hcase131a hcase321a hcase140b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase40 hcase42 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase101a hcase041a hcase340b hcase411a hcase411b hcase330b hcase301a hcase110b hcase120b hcase131a hcase321a hcase141a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase40 hcase42 hcase43
                        omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase411b hcase330a hcase330b hcase441a hcase441b hcase110a hcase110b hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase14 hcase31 hcase32 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase330a hcase330b hcase301a hcase301b hcase441a hcase441b hcase110a hcase110b hcase121a hcase121b hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase13 hcase14 hcase31 hcase32 hcase42 hcase43
                    omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase330a hcase330b hcase301a hcase301b hcase441a hcase441b hcase111a hcase111b hcase130b hcase00 hcase01 hcase02 hcase03 hcase10 hcase12 hcase14 hcase31 hcase32 hcase40 hcase42 hcase43
                  omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase330a hcase330b hcase301a hcase301b hcase441a hcase441b hcase111a hcase111b hcase131a hcase140a hcase140b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase12 hcase31 hcase40 hcase42 hcase43
                      omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020b hcase010a hcase010b hcase001a hcase041a hcase340b hcase411a hcase411b hcase330b hcase301a hcase111a hcase111b hcase131a hcase131b hcase140a hcase140b hcase321a hcase310b hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase12 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase330a hcase330b hcase301a hcase301b hcase441a hcase441b hcase111a hcase111b hcase131a hcase131b hcase140a hcase140b hcase321a hcase321b hcase310a hcase310b hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase12 hcase42 hcase43
                          omega
                      ·
                        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                        ·
                          clear hn4 hcut28 hcut3 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase101a hcase041a hcase340a hcase340b hcase411a hcase330b hcase301a hcase111a hcase131a hcase140b hcase321a hcase311a hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase40 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase340a hcase340b hcase411a hcase411b hcase330a hcase330b hcase301a hcase301b hcase441a hcase441b hcase111a hcase131a hcase140a hcase140b hcase321a hcase321b hcase311a hcase311b hcase121a hcase00 hcase01 hcase02 hcase03 hcase10 hcase40 hcase42 hcase43
                          omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase340a hcase340b hcase411a hcase411b hcase330a hcase330b hcase301a hcase301b hcase441a hcase441b hcase111a hcase131a hcase141a hcase00 hcase01 hcase02 hcase03 hcase10 hcase12 hcase31 hcase32 hcase40 hcase42 hcase43
                    omega
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340b hcase331a hcase300b hcase310b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  clear hn4 hsum_nat1 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010a hcase010b hcase001a hcase041a hcase340b hcase411a hcase331a hcase300b hcase310b hcase321a hcase430b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase42 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase331a hcase331b hcase300a hcase300b hcase310a hcase310b hcase321a hcase321b hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase42 hcase44
                  omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase331a hcase331b hcase300a hcase300b hcase311a hcase311b hcase400a hcase400b hcase130b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase331a hcase331b hcase300a hcase300b hcase400b hcase131a hcase131b hcase420a hcase420b hcase440b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase43
                      omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut31 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase331a hcase331b hcase300a hcase300b hcase311a hcase311b hcase400b hcase131a hcase420b hcase441a hcase430b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase32
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase331a hcase331b hcase300a hcase300b hcase311a hcase311b hcase400a hcase400b hcase131a hcase131b hcase420a hcase420b hcase441a hcase441b hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase32
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase331a hcase331b hcase300a hcase300b hcase311a hcase311b hcase400a hcase400b hcase131a hcase131b hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase32 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase331a hcase331b hcase300a hcase300b hcase311a hcase311b hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase32 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase331a hcase331b hcase301a hcase301b hcase120a hcase120b hcase130b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase14 hcase31 hcase32 hcase40 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase340a hcase340b hcase411a hcase411b hcase331a hcase331b hcase301a hcase301b hcase120b hcase131a hcase110b hcase140b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          clear hn4 hcut28 hcut53 hcut51 hcut21 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase101a hcase041a hcase340a hcase340b hcase411a hcase331b hcase301b hcase120b hcase131a hcase110b hcase140b hcase321a hcase400b hcase430b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase331a hcase331b hcase301a hcase301b hcase120a hcase120b hcase131a hcase131b hcase110a hcase110b hcase140a hcase140b hcase321a hcase321b hcase400a hcase400b hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase42 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase331a hcase331b hcase301a hcase301b hcase120a hcase120b hcase131a hcase131b hcase110a hcase110b hcase140a hcase140b hcase321a hcase321b hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase411b hcase331a hcase331b hcase301a hcase301b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase430a hcase430b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase40 hcase42 hcase44
                        omega
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010a hcase010b hcase001a hcase101a hcase041a hcase340b hcase411a hcase331a hcase301a hcase120b hcase131a hcase110b hcase141a hcase430b hcase321a hcase310b hcase00 hcase01 hcase02 hcase03 hcase10 hcase40 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase411b hcase331a hcase301a hcase120a hcase120b hcase131a hcase131b hcase110a hcase110b hcase141a hcase141b hcase430a hcase430b hcase321a hcase311a hcase00 hcase01 hcase02 hcase03 hcase10 hcase40 hcase42 hcase44
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase331a hcase331b hcase301a hcase301b hcase120a hcase120b hcase131a hcase131b hcase110a hcase110b hcase141a hcase141b hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase32 hcase40 hcase42 hcase44
                      omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase411b hcase331a hcase331b hcase301a hcase301b hcase120a hcase120b hcase111a hcase111b hcase140a hcase140b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hcut28 hcut51 hcut21 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase101a hcase041a hcase340a hcase340b hcase411a hcase331b hcase301b hcase120b hcase131a hcase111a hcase140b hcase321a hcase430b hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase331a hcase331b hcase301a hcase301b hcase120a hcase120b hcase131a hcase131b hcase111a hcase111b hcase140a hcase140b hcase321a hcase321b hcase430a hcase430b hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase42 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase331a hcase331b hcase301a hcase301b hcase120a hcase120b hcase131a hcase131b hcase111a hcase111b hcase140a hcase140b hcase321a hcase321b hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase40 hcase42 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase340a hcase340b hcase411a hcase411b hcase331a hcase331b hcase301a hcase301b hcase120a hcase120b hcase131a hcase111a hcase141a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase32 hcase40 hcase42 hcase43 hcase44
                    omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase411b hcase331a hcase331b hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase31 hcase32 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase340a hcase340b hcase411a hcase331a hcase331b hcase301a hcase301b hcase121a hcase121b hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase31 hcase32 hcase42 hcase43 hcase44
                omega
    ·
      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
      ·
        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
        ·
          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase041a hcase341a hcase341b hcase300a hcase300b hcase420b hcase440a hcase440b hcase410b hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase43
                omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase420b hcase440b hcase410a hcase410b hcase401a hcase430b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase420a hcase420b hcase440a hcase440b hcase410a hcase410b hcase401a hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33
                  omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase300a hcase300b hcase420a hcase420b hcase440b hcase411a hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase43
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase420a hcase420b hcase440a hcase440b hcase411a hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase43
                omega
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase341a hcase341b hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase320a hcase320b hcase130b hcase140b hcase310a hcase310b hcase120b hcase110b hcase00 hcase01 hcase02 hcase03 hcase10 hcase33 hcase40 hcase41 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase320a hcase320b hcase130b hcase140a hcase140b hcase310a hcase310b hcase120b hcase111a hcase00 hcase01 hcase02 hcase03 hcase10 hcase33 hcase40 hcase41 hcase43
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase320b hcase130a hcase130b hcase140a hcase140b hcase310b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase33 hcase40 hcase41 hcase43
                      omega
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase320a hcase320b hcase130a hcase130b hcase140a hcase140b hcase110a hcase110b hcase330a hcase330b hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase40 hcase41 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase320b hcase130a hcase130b hcase140a hcase140b hcase311a hcase110a hcase110b hcase330b hcase121a hcase00 hcase01 hcase02 hcase03 hcase10 hcase40 hcase41 hcase43
                          omega
                      ·
                        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                        ·
                          clear hn4 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010b hcase001a hcase101a hcase041a hcase300a hcase300b hcase420a hcase420b hcase441a hcase320a hcase320b hcase130b hcase140b hcase311a hcase311b hcase110b hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase40 hcase41 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase320b hcase130a hcase130b hcase140a hcase140b hcase311a hcase110a hcase110b hcase331a hcase121a hcase00 hcase01 hcase02 hcase03 hcase10 hcase40 hcase41 hcase43
                          omega
                    ·
                      rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase320a hcase320b hcase130a hcase130b hcase140a hcase140b hcase111a hcase111b hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase33 hcase40 hcase41 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010b hcase001a hcase101a hcase101b hcase041a hcase341a hcase300b hcase420a hcase420b hcase441a hcase320b hcase130a hcase130b hcase140a hcase140b hcase311a hcase121a hcase00 hcase01 hcase02 hcase03 hcase10 hcase33 hcase40 hcase41 hcase43
                        omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase320a hcase320b hcase130b hcase141a hcase330a hcase330b hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase31 hcase40 hcase41 hcase43
                      omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase341a hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase320b hcase130b hcase141a hcase330b hcase121a hcase310b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase40 hcase41 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase320b hcase130a hcase130b hcase141a hcase141b hcase330b hcase121a hcase311a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase40 hcase41 hcase43
                        omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase341a hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase320b hcase130b hcase141a hcase331a hcase310b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase40 hcase41 hcase43
                      omega
                    ·
                      rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase320a hcase320b hcase130b hcase141a hcase331a hcase331b hcase311a hcase311b hcase120b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase40 hcase41 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase320b hcase130a hcase130b hcase141a hcase141b hcase331a hcase311a hcase121a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase40 hcase41 hcase43
                        omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase33 hcase40 hcase41 hcase43
                omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut31 hcut39 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020b hcase010b hcase001a hcase041a hcase341a hcase341b hcase300a hcase300b hcase420b hcase441a hcase321a hcase321b hcase400b hcase130b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase33 hcase41 hcase43
                  omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase420b hcase441a hcase321a hcase321b hcase400b hcase131a hcase131b hcase410b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase33 hcase43
                    omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut31 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase420b hcase441a hcase321a hcase321b hcase400b hcase131a hcase411a hcase430b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase33
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase321a hcase321b hcase400a hcase400b hcase131a hcase131b hcase411a hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase14 hcase31 hcase33
                      omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010a hcase010b hcase001a hcase101a hcase101b hcase041a hcase341a hcase341b hcase300a hcase300b hcase420b hcase441a hcase401a hcase410b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase43
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase420a hcase420b hcase441a hcase441b hcase321a hcase321b hcase401a hcase411a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase43
                  omega
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase40 hcase41 hcase43 hcase44
            omega
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase041a hcase341a hcase341b hcase300a hcase300b hcase421a hcase321a hcase410b hcase430b hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase421a hcase321a hcase321b hcase410a hcase410b hcase430a hcase430b hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase421a hcase321a hcase321b hcase410a hcase410b hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase40 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase300a hcase300b hcase421a hcase321a hcase321b hcase411a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase40 hcase43 hcase44
              omega
      ·
        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase341a hcase341b hcase301a hcase301b hcase120b hcase130b hcase140b hcase110b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120b hcase130b hcase140a hcase140b hcase111a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120b hcase130b hcase141a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase110a hcase110b hcase140a hcase140b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase101a hcase041a hcase120b hcase131a hcase110b hcase140b hcase321a hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase33 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      clear hn4 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut37 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase101a hcase041a hcase301a hcase301b hcase120b hcase131a hcase110b hcase140b hcase321a hcase401a hcase430b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase33 hcase41 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase131a hcase131b hcase110a hcase110b hcase140a hcase140b hcase321a hcase321b hcase401a hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase33 hcase41 hcase42 hcase44
                      omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase430a hcase430b hcase310a hcase310b hcase330a hcase330b hcase400a hcase400b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase41 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut31 hcut39 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase101a hcase041a hcase341a hcase341b hcase120b hcase131a hcase110b hcase141a hcase430b hcase310a hcase310b hcase330a hcase330b hcase400b hcase321a hcase00 hcase01 hcase02 hcase03 hcase10 hcase41 hcase42 hcase44
                          omega
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase430a hcase430b hcase310a hcase310b hcase330a hcase330b hcase401a hcase401b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase41 hcase42 hcase44
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut64 hcut37 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010a hcase010b hcase001a hcase101a hcase041a hcase341a hcase301a hcase120b hcase131a hcase110b hcase141a hcase430b hcase310b hcase330b hcase401a hcase321a hcase420b hcase00 hcase01 hcase02 hcase03 hcase10 hcase41 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase131a hcase131b hcase110a hcase110b hcase141a hcase141b hcase430a hcase430b hcase310a hcase310b hcase330a hcase330b hcase401a hcase321a hcase321b hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase41 hcase44
                            omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase430a hcase430b hcase310a hcase310b hcase331a hcase331b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase40 hcase41 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase301a hcase120a hcase120b hcase131a hcase131b hcase110a hcase110b hcase141a hcase141b hcase430a hcase430b hcase310a hcase310b hcase331a hcase321a hcase00 hcase01 hcase02 hcase03 hcase10 hcase40 hcase41 hcase42 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120b hcase131a hcase131b hcase110a hcase110b hcase141a hcase141b hcase430a hcase430b hcase00 hcase01 hcase02 hcase03 hcase10 hcase32 hcase33 hcase40 hcase41 hcase42 hcase44
                    omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010b hcase001a hcase101a hcase041a hcase341a hcase341b hcase120b hcase110b hcase141a hcase431a hcase400b hcase410b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase33 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase110a hcase110b hcase141a hcase141b hcase431a hcase400b hcase410b hcase321a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase33 hcase42 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase131a hcase131b hcase110a hcase110b hcase141a hcase141b hcase431a hcase400a hcase400b hcase411a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase32 hcase33 hcase42 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase131a hcase131b hcase110a hcase110b hcase141a hcase141b hcase431a hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase32 hcase33 hcase41 hcase42 hcase44
                    omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010b hcase001a hcase101a hcase041a hcase341b hcase301b hcase120a hcase120b hcase111a hcase410b hcase140b hcase400b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase33 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut57 hcut64 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010b hcase001a hcase101a hcase041a hcase120a hcase120b hcase131a hcase111a hcase410b hcase140b hcase400b hcase321a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase33 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hcut28 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase341a hcase341b hcase301a hcase301b hcase120b hcase111a hcase410b hcase140b hcase401a hcase430b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase33 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut28 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase101a hcase041a hcase301a hcase301b hcase120b hcase111a hcase410b hcase140b hcase401a hcase430b hcase321a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase33 hcase42 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase131a hcase131b hcase111a hcase111b hcase410a hcase410b hcase140a hcase140b hcase401a hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase32 hcase33 hcase42 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase131a hcase111a hcase410a hcase410b hcase141a hcase00 hcase01 hcase02 hcase03 hcase10 hcase31 hcase32 hcase33 hcase40 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase111a hcase111b hcase411a hcase411b hcase430a hcase430b hcase400a hcase400b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase14 hcase31 hcase33 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut28 hcut53 hcut51 hcut21 hcut31 hcut39 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase041a hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase131a hcase111a hcase111b hcase411a hcase430b hcase400b hcase321a hcase00 hcase01 hcase02 hcase03 hcase10 hcase14 hcase31 hcase33 hcase42 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase131a hcase131b hcase111a hcase111b hcase411a hcase430a hcase430b hcase401a hcase00 hcase01 hcase02 hcase03 hcase10 hcase14 hcase31 hcase32 hcase33 hcase42 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase120a hcase120b hcase131a hcase131b hcase111a hcase111b hcase411a hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase14 hcase31 hcase32 hcase33 hcase40 hcase42 hcase44
                  omega
        ·
          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase301a hcase310b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase310a hcase310b hcase321a hcase321b hcase330a hcase330b hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030b hcase020b hcase010a hcase010b hcase001a hcase101a hcase101b hcase041a hcase341a hcase301a hcase310b hcase321a hcase330b hcase401a hcase410b hcase420b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase121a hcase121b hcase310a hcase310b hcase321a hcase321b hcase330a hcase330b hcase401a hcase410a hcase410b hcase421a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase341b hcase301a hcase301b hcase121a hcase121b hcase310a hcase310b hcase321a hcase321b hcase330a hcase330b hcase401a hcase411a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase42 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase301a hcase121a hcase121b hcase310a hcase310b hcase321a hcase331a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase301a hcase121a hcase311a hcase330b hcase320b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase301a hcase121a hcase121b hcase311a hcase330a hcase330b hcase321a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut28 hcut3 hcut53 hcut51 hcut21 hcut6 hcut31 hcut39 hcut15 hcut57 hcut64 hcut37 hcut45 hcut65 hcut33 hcut48 hcut26 hcut29 hcut38 hcut0 hcut22 hcut43 hcut40 hcut62 hcut59 hcut66 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase030a hcase030b hcase020a hcase020b hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase041a hcase041b hcase341a hcase301a hcase121a hcase121b hcase311a hcase331a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega

#print axioms symbolic_v2_mask515_integer_shard002
end Jsp404.SixExactFloorKernel
