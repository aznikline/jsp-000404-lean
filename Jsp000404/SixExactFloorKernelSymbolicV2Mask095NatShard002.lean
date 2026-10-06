import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask95_integer_shard002 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut11 : (s02 + s03 + s40 + s41 + s42 + u02 + u03 + u40 + u41 + u42) + 1 ≤ (n + 1))
    (hcut9 : (s02 + s40 + s41 + s42 + u02 + u40 + u41 + u42) + 1 ≤ (n))
    (hcut40 : (s12 + s30 + s31 + u12 + u30 + u31 + 1) + 1 ≤ (n))
    (hcut18 : (s00 + s13 + s40 + u00 + u13 + u40) + 1 ≤ (2 * n))
    (hcut22 : (s11 + s12 + u11 + u12 + 2) + 1 ≤ (n))
    (hcut81 : (s00 + s33 + s44 + u00 + u33 + u44) + 1 ≤ (n + 2))
    (hcut0 : (s11 + s12 + s30 + s31 + s34 + s41 + s42 + s43 + u11 + u12 + u30 + u31 + u34 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut10 : (s01 + s43 + u01 + u43) + 1 ≤ (s33 + 2))
    (hcut32 : (s11 + s30 + s31 + u11 + u30 + u31 + 2) + 1 ≤ (n))
    (hcut13 : (s00 + s13 + s33 + s40 + u00 + u13 + u33 + u40) + 1 ≤ (2 * n + 1))
    (hcut30 : (s11 + s14 + s31 + u11 + u14 + u31 + 2) + 1 ≤ (n))
    (hcut52 : (s31 + u31) + 1 ≤ (s10 + 1))
    (hcut14 : (s00 + s33 + u00 + u33) + 1 ≤ (n + 1))
    (hcut82 : (s11 + s13 + s14 + s40 + s42 + s43 + u11 + u13 + u14 + u40 + u42 + u43 + 1) + 1 ≤ (2 * n))
    (hcut71 : (s02 + s03 + s10 + s14 + s42 + u02 + u03 + u10 + u14 + u42) + 1 ≤ (n))
    (hcut91 : (s01 + s02 + s03 + s10 + s14 + s32 + u01 + u02 + u03 + u10 + u14 + u32) + 1 ≤ (n + 1))
    (hcut45 : (s12 + s14 + s42 + u12 + u14 + u42 + 1) + 1 ≤ (n))
    (hcut61 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 1))
    (hcut63 : (s00 + s04 + s13 + s40 + s44 + u00 + u04 + u13 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut23 : (s10 + s32 + s40 + u10 + u32 + u40 + 2) + 1 ≤ (2 * n))
    (hcut47 : (s11 + s12 + s30 + u11 + u12 + u30 + 1) + 1 ≤ (n))
    (hcut2 : (s44 + u44) + 1 ≤ (s34 + 3))
    (hcut37 : (s14 + s40 + u14 + u40) + 1 ≤ (n))
    (hcut1 : (s00 + s04 + s13 + s33 + s40 + s44 + u00 + u04 + u13 + u33 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut68 : (s02 + s03 + s14 + s41 + s42 + u02 + u03 + u14 + u41 + u42) + 1 ≤ (n))
    (hcut39 : (s41 + u41) + 1 ≤ (s13 + 1))
    (hcut86 : (s11 + s12 + s13 + s14 + u11 + u12 + u13 + u14) + 1 ≤ (n))
    (hcut15 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut46 : (s03 + u03) + 1 ≤ (s13 + 1))
    (hcut59 : (s02 + u02) + 1 ≤ (s13 + 2))
    (hcut20 : (s34 + u34) + 1 ≤ (s44 + 2))
    (hcut35 : (s01 + s10 + u01 + u10) + 1 ≤ (n))
    (hcut89 : (s01 + s13 + s40 + s44 + u01 + u13 + u40 + u44) + 1 ≤ (2 * n))
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
    (hcase101a : 1 ≤ s10)
    (hcase101b : u10 = 1)
    (hcase010a : s01 = 0)
    (hcase010b : u01 = 0)
    (hcase040a : s04 = 0)
    (hcase040b : u04 = 0)
    : False := by
  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
  ·
    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
    ·
      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
      ·
        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020b hcase400b hcase030b hcase410b hcase430b hcase420b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020a hcase020b hcase400b hcase030a hcase030b hcase410b hcase430b hcase421a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330b hcase020a hcase020b hcase400a hcase400b hcase030a hcase030b hcase410a hcase410b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase42 hcase44
                  omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101b hcase010a hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330b hcase020b hcase400b hcase030b hcase411a hcase420b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020a hcase020b hcase400a hcase400b hcase030a hcase030b hcase411a hcase421a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase43 hcase44
                  omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310b hcase330b hcase020a hcase020b hcase400a hcase400b hcase031a hcase031b hcase320b hcase340b hcase300b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330b hcase020a hcase020b hcase400a hcase400b hcase031a hcase031b hcase320b hcase340b hcase301a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hn4 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101b hcase010b hcase040b hcase140a hcase140b hcase310b hcase330b hcase020b hcase400a hcase400b hcase031a hcase320b hcase341a hcase300b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101b hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330b hcase020b hcase400b hcase031a hcase320b hcase341a hcase301a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101b hcase010a hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330b hcase020b hcase400b hcase031a hcase321a hcase321b hcase420b hcase410b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase34 hcase43 hcase44
                    omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut37 hcut1 hcut68 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020a hcase020b hcase400b hcase031a hcase031b hcase321a hcase321b hcase420b hcase411a hcase340b hcase430b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020a hcase020b hcase400a hcase400b hcase031a hcase031b hcase321a hcase321b hcase420a hcase420b hcase411a hcase340a hcase340b hcase431a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase44
                        omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020a hcase020b hcase400b hcase031a hcase031b hcase321a hcase321b hcase420b hcase411a hcase341a hcase341b hcase430b hcase440b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330b hcase020a hcase020b hcase400b hcase031a hcase321a hcase420a hcase420b hcase411a hcase341a hcase430a hcase430b hcase441a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020a hcase020b hcase400a hcase400b hcase031a hcase031b hcase321a hcase321b hcase420a hcase420b hcase411a hcase341a hcase341b hcase431a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase44
                        omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330b hcase020a hcase020b hcase400b hcase031a hcase321a hcase321b hcase421a hcase410b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase34 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020a hcase020b hcase400a hcase400b hcase031a hcase031b hcase321a hcase321b hcase421a hcase411a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase34 hcase43 hcase44
                    omega
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          clear hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310b hcase330b hcase020a hcase020b hcase401a hcase401b hcase410a hcase410b hcase430a hcase430b hcase440a hcase440b hcase030a hcase030b hcase320b hcase340b hcase300b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase42
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330b hcase020a hcase020b hcase401a hcase401b hcase410a hcase410b hcase430a hcase430b hcase440a hcase440b hcase030a hcase030b hcase320b hcase340b hcase301a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase42
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020a hcase020b hcase401a hcase401b hcase410a hcase410b hcase430a hcase430b hcase440b hcase030a hcase030b hcase320a hcase320b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase42
                        omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                          ·
                            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                            ·
                              clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040b hcase140b hcase310a hcase310b hcase330a hcase330b hcase020b hcase401a hcase410b hcase430b hcase440b hcase030b hcase340a hcase340b hcase420b hcase120b hcase110b hcase00 hcase01 hcase04 hcase10 hcase13 hcase30
                              omega
                            ·
                              clear hn4 hcut11 hcut9 hcut40 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040b hcase140b hcase310a hcase310b hcase330b hcase020b hcase401a hcase410b hcase430b hcase440b hcase030b hcase321a hcase340b hcase420b hcase120b hcase111a hcase00 hcase01 hcase04 hcase10 hcase13 hcase30
                              omega
                          ·
                            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                            ·
                              clear hn4 hsum_nat0 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140b hcase310b hcase330b hcase020a hcase020b hcase401a hcase410b hcase430b hcase440b hcase030a hcase030b hcase321a hcase340b hcase420b hcase121a hcase130b hcase00 hcase01 hcase04 hcase10 hcase11 hcase30
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020b hcase401a hcase410b hcase430b hcase440b hcase030b hcase321a hcase321b hcase340a hcase340b hcase420b hcase121a hcase121b hcase00 hcase01 hcase04 hcase10 hcase11 hcase30
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020a hcase020b hcase401a hcase410a hcase410b hcase430a hcase430b hcase440a hcase440b hcase030a hcase030b hcase321a hcase321b hcase340a hcase340b hcase421a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020a hcase020b hcase401a hcase401b hcase410a hcase410b hcase430a hcase430b hcase440b hcase030a hcase030b hcase321a hcase321b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase42
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020a hcase020b hcase401a hcase410a hcase410b hcase430b hcase440b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase42
                    omega
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020b hcase401a hcase401b hcase410a hcase410b hcase430a hcase430b hcase030b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase42
                    omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020b hcase401a hcase401b hcase410a hcase410b hcase430a hcase430b hcase031a hcase420a hcase420b hcase130b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase32 hcase34
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020b hcase401a hcase410b hcase430b hcase441a hcase031a hcase420b hcase131a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase32 hcase34
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020a hcase020b hcase401a hcase410a hcase410b hcase430a hcase430b hcase441a hcase441b hcase031a hcase031b hcase421a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34
                      omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020a hcase020b hcase401a hcase410a hcase410b hcase431a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase42 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase020a hcase020b hcase401a hcase411a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
          ·
            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  clear hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310b hcase330b hcase021a hcase021b hcase030a hcase030b hcase340b hcase320b hcase300b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330b hcase021a hcase021b hcase030a hcase030b hcase340b hcase320b hcase301a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase021a hcase030a hcase030b hcase340a hcase340b hcase430b hcase400b hcase420b hcase410b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut37 hcut1 hcut68 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase021a hcase021b hcase030a hcase030b hcase340b hcase321a hcase321b hcase430b hcase400b hcase420b hcase411a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase44
                        omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase021a hcase030a hcase030b hcase340a hcase340b hcase321a hcase321b hcase430b hcase400b hcase421a hcase410b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase021a hcase021b hcase030a hcase030b hcase340a hcase340b hcase321a hcase321b hcase430a hcase430b hcase400a hcase400b hcase421a hcase411a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase44
                        omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase030a hcase030b hcase340a hcase340b hcase321a hcase321b hcase430b hcase401a hcase440b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase41 hcase42
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase021a hcase030b hcase340a hcase340b hcase321a hcase321b hcase430b hcase401a hcase441a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase41 hcase42
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330b hcase021a hcase021b hcase030a hcase030b hcase340a hcase340b hcase321a hcase321b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase40 hcase41 hcase42 hcase44
                  omega
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase021a hcase021b hcase030a hcase030b hcase300a hcase300b hcase440b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase32 hcase40 hcase41 hcase42 hcase43
                  omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase040b hcase140a hcase140b hcase310b hcase330b hcase021a hcase030a hcase030b hcase341a hcase300b hcase441a hcase320b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase140a hcase140b hcase310b hcase330b hcase021a hcase030a hcase030b hcase341a hcase300b hcase441a hcase321a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43
                    omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase030a hcase030b hcase341a hcase341b hcase301a hcase301b hcase430b hcase410a hcase410b hcase440b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase32 hcase40 hcase42
                      omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase021a hcase030a hcase030b hcase341a hcase341b hcase301a hcase301b hcase430b hcase410b hcase441a hcase400b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase32 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase021a hcase030b hcase341a hcase341b hcase301a hcase301b hcase430b hcase410a hcase410b hcase441a hcase401a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase32 hcase42
                        omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330b hcase021a hcase021b hcase030a hcase030b hcase341a hcase301a hcase430a hcase430b hcase400a hcase400b hcase320b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase330b hcase021a hcase030a hcase030b hcase341a hcase301a hcase430a hcase430b hcase411a hcase400b hcase321a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase42 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase021a hcase021b hcase030a hcase030b hcase341a hcase341b hcase301a hcase301b hcase430a hcase430b hcase411a hcase401a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase32 hcase42 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330b hcase021a hcase021b hcase030a hcase030b hcase341a hcase341b hcase301a hcase301b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase32 hcase40 hcase41 hcase42 hcase44
                  omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase330a hcase330b hcase021a hcase031a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
      ·
        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
        ·
          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
          ·
            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase400a hcase400b hcase030b hcase020b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase400b hcase030a hcase030b hcase021a hcase430b hcase410b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase42 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase400a hcase400b hcase030b hcase021a hcase430b hcase411a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase42 hcase44
                  omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase331a hcase400b hcase030a hcase030b hcase021a hcase431a hcase410b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase42 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase331a hcase331b hcase400a hcase400b hcase030a hcase030b hcase021a hcase021b hcase431a hcase411a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase42 hcase44
                  omega
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101b hcase010a hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase331a hcase400b hcase031a hcase410b hcase020b hcase420b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase331a hcase400b hcase031a hcase410b hcase020a hcase020b hcase421a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase331a hcase331b hcase400a hcase400b hcase031a hcase410a hcase410b hcase021a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase400b hcase031a hcase411a hcase430b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase42 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase331a hcase331b hcase400a hcase400b hcase031a hcase031b hcase411a hcase431a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase42 hcase44
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
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase401a hcase401b hcase410a hcase410b hcase420a hcase420b hcase430a hcase430b hcase020b hcase030b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase44
                    omega
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase331a hcase331b hcase401a hcase401b hcase410a hcase410b hcase420a hcase420b hcase430a hcase430b hcase020a hcase020b hcase130b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase32 hcase34 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase401a hcase410b hcase420b hcase430b hcase020b hcase031a hcase131a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase32 hcase34 hcase44
                      omega
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase310a hcase310b hcase401a hcase410a hcase410b hcase420a hcase420b hcase430b hcase021a hcase030b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase331a hcase331b hcase401a hcase401b hcase410a hcase410b hcase420a hcase420b hcase430a hcase430b hcase021a hcase031a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase331a hcase331b hcase401a hcase410a hcase410b hcase420a hcase420b hcase431a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase331a hcase331b hcase401a hcase410a hcase410b hcase421a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase43 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase310a hcase310b hcase331a hcase331b hcase401a hcase411a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase34 hcase42 hcase43 hcase44
            omega
    ·
      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
      ·
        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase130a hcase130b hcase020a hcase020b hcase300a hcase300b hcase320b hcase330b hcase340b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase130a hcase130b hcase020a hcase020b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase440b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase311b hcase130b hcase020b hcase300a hcase300b hcase320a hcase320b hcase330a hcase330b hcase341a hcase341b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase43
                    omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase311b hcase130b hcase020b hcase300a hcase300b hcase320a hcase320b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010a hcase010b hcase040b hcase140a hcase140b hcase311b hcase130b hcase020b hcase300a hcase300b hcase321b hcase330a hcase330b hcase400b hcase120a hcase120b hcase110a hcase110b hcase420b hcase00 hcase01 hcase03 hcase04 hcase10 hcase34 hcase41 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase130b hcase020a hcase020b hcase300a hcase300b hcase321a hcase321b hcase330a hcase330b hcase400a hcase400b hcase120b hcase110b hcase00 hcase01 hcase03 hcase04 hcase10 hcase34 hcase41 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase140a hcase140b hcase130b hcase020a hcase020b hcase300a hcase300b hcase321a hcase321b hcase330b hcase400b hcase120b hcase111a hcase00 hcase01 hcase03 hcase04 hcase10 hcase34 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hcut11 hcut9 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase140a hcase140b hcase130b hcase020a hcase020b hcase300a hcase300b hcase321a hcase330b hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase34 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040b hcase140a hcase140b hcase311a hcase130b hcase020b hcase300b hcase321a hcase330b hcase401a hcase420b hcase430b hcase340b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41 hcase44
                        omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase130b hcase020a hcase020b hcase300b hcase321a hcase330b hcase401a hcase420b hcase430b hcase341a hcase440b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase311b hcase130b hcase020b hcase300a hcase300b hcase321a hcase321b hcase330a hcase330b hcase401a hcase401b hcase420a hcase420b hcase430a hcase430b hcase341a hcase341b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase130a hcase130b hcase020a hcase020b hcase300a hcase300b hcase321a hcase321b hcase330a hcase330b hcase401a hcase420a hcase420b hcase431a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase34 hcase41 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase130a hcase130b hcase020a hcase020b hcase300a hcase300b hcase321a hcase321b hcase330a hcase330b hcase401a hcase421a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase34 hcase41 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase311b hcase130b hcase020b hcase300a hcase300b hcase321a hcase321b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase130a hcase130b hcase020a hcase020b hcase301a hcase120a hcase120b hcase330b hcase340b hcase320b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase130b hcase020a hcase020b hcase301a hcase120b hcase330b hcase340b hcase321a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase130b hcase020b hcase301a hcase120a hcase120b hcase330b hcase341a hcase320b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase130a hcase130b hcase020a hcase020b hcase301a hcase120a hcase120b hcase330a hcase330b hcase341a hcase321a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase311b hcase130b hcase020b hcase301a hcase301b hcase120a hcase120b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase130a hcase130b hcase020a hcase020b hcase301a hcase330b hcase320b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut9 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase130b hcase020a hcase020b hcase301a hcase121a hcase330b hcase321a hcase110b hcase340b hcase00 hcase01 hcase03 hcase04 hcase10 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase130a hcase130b hcase020a hcase020b hcase301a hcase121a hcase121b hcase330a hcase330b hcase321a hcase110a hcase110b hcase341a hcase00 hcase01 hcase03 hcase04 hcase10 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase140a hcase140b hcase130b hcase020a hcase020b hcase121a hcase330b hcase321a hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase34 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase140b hcase311a hcase130b hcase020a hcase020b hcase301a hcase121a hcase330b hcase321a hcase111a hcase401a hcase00 hcase01 hcase03 hcase04 hcase10 hcase34 hcase41 hcase42 hcase43 hcase44
                      omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase311b hcase130b hcase020b hcase301a hcase301b hcase121a hcase121b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase130b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
        ·
          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase131b hcase030a hcase030b hcase330b hcase320b hcase300b hcase340b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase131b hcase030a hcase030b hcase330b hcase320b hcase300b hcase341a hcase440b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase43
                    omega
                  ·
                    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                    ·
                      clear hn4 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase131b hcase030b hcase330b hcase320b hcase300b hcase341a hcase441a hcase020b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase030a hcase030b hcase330b hcase320b hcase300b hcase341a hcase441a hcase021a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase43
                      omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase030b hcase330b hcase320b hcase400b hcase020b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase34 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase030a hcase030b hcase330b hcase320b hcase301a hcase400b hcase021a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase34 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase030a hcase030b hcase330b hcase320b hcase301a hcase401a hcase401b hcase340b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase030b hcase330b hcase320b hcase301a hcase401a hcase401b hcase341a hcase020b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase030a hcase030b hcase330b hcase320b hcase301a hcase401a hcase341a hcase440b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut11 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase030b hcase330b hcase320b hcase301a hcase401a hcase341a hcase021a hcase441a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43
                        omega
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase030a hcase030b hcase330b hcase321a hcase430b hcase020a hcase020b hcase410b hcase420b hcase440b hcase340b hcase300b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase40
                            omega
                          ·
                            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                            ·
                              clear hn4 hcut11 hcut9 hcut40 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040b hcase140b hcase311a hcase131a hcase030b hcase330b hcase321a hcase430b hcase020b hcase410b hcase420b hcase440b hcase340b hcase301a hcase120b hcase00 hcase01 hcase04 hcase10 hcase11 hcase40
                              omega
                            ·
                              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                              ·
                                clear hn4 hcut11 hcut9 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040b hcase140b hcase311a hcase131a hcase030b hcase330b hcase321a hcase430b hcase020b hcase410b hcase420b hcase440b hcase340b hcase301a hcase121a hcase110b hcase00 hcase01 hcase04 hcase10 hcase40
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase030a hcase030b hcase330a hcase330b hcase321a hcase321b hcase430a hcase430b hcase020a hcase020b hcase410a hcase410b hcase420a hcase420b hcase440a hcase440b hcase340a hcase340b hcase301a hcase301b hcase121a hcase111a hcase00 hcase01 hcase04 hcase10 hcase40
                                omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030a hcase030b hcase330a hcase330b hcase321a hcase321b hcase430a hcase430b hcase020a hcase020b hcase410a hcase410b hcase420a hcase420b hcase440b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase40
                          omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030b hcase330a hcase330b hcase321a hcase321b hcase430a hcase430b hcase020b hcase410a hcase410b hcase420a hcase420b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase34 hcase40
                        omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase131a hcase131b hcase030a hcase030b hcase330a hcase330b hcase321a hcase321b hcase430a hcase430b hcase020a hcase020b hcase410a hcase410b hcase421a hcase440b hcase400b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase34
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030a hcase030b hcase330a hcase330b hcase321a hcase321b hcase430a hcase430b hcase020a hcase020b hcase410a hcase410b hcase421a hcase440a hcase440b hcase401a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase34
                          omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030b hcase330a hcase330b hcase321a hcase321b hcase430a hcase430b hcase020b hcase410a hcase410b hcase421a hcase421b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase34 hcase40
                        omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase030b hcase330a hcase330b hcase321a hcase321b hcase430b hcase020b hcase411a hcase400b hcase420b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase34 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030a hcase030b hcase330a hcase330b hcase321a hcase321b hcase430a hcase430b hcase020a hcase020b hcase411a hcase400a hcase400b hcase421a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase34 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030a hcase030b hcase330a hcase330b hcase321a hcase321b hcase430a hcase430b hcase020a hcase020b hcase411a hcase401a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase34 hcase42 hcase44
                      omega
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase030a hcase030b hcase330b hcase321a hcase430a hcase430b hcase340b hcase300b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase44
                      omega
                    ·
                      rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase030a hcase030b hcase330b hcase321a hcase430a hcase430b hcase021a hcase340a hcase340b hcase301a hcase120a hcase120b hcase400b hcase00 hcase01 hcase04 hcase10 hcase11 hcase41 hcase42 hcase44
                          omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              clear hn4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase131a hcase030a hcase030b hcase330b hcase321a hcase430b hcase021a hcase340b hcase301a hcase120b hcase401a hcase410b hcase420b hcase00 hcase01 hcase04 hcase10 hcase11 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030a hcase030b hcase330a hcase330b hcase321a hcase321b hcase430a hcase430b hcase021a hcase021b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase401a hcase410a hcase410b hcase421a hcase00 hcase01 hcase04 hcase10 hcase11 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030a hcase030b hcase330a hcase330b hcase321a hcase321b hcase430a hcase430b hcase021a hcase021b hcase340a hcase340b hcase301a hcase301b hcase120a hcase120b hcase401a hcase411a hcase00 hcase01 hcase04 hcase10 hcase11 hcase42 hcase44
                            omega
                      ·
                        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat1 hcut11 hcut9 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase030a hcase030b hcase330b hcase321a hcase430b hcase021a hcase340b hcase301a hcase110a hcase110b hcase410b hcase420b hcase400b hcase00 hcase01 hcase04 hcase10 hcase44
                                omega
                              ·
                                clear hn4 hcut11 hcut9 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase131a hcase030a hcase030b hcase330b hcase321a hcase430b hcase021a hcase340b hcase301a hcase121a hcase110b hcase410b hcase420b hcase401a hcase00 hcase01 hcase04 hcase10 hcase44
                                omega
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase030a hcase030b hcase330b hcase321a hcase430a hcase430b hcase021a hcase340a hcase340b hcase301a hcase110a hcase110b hcase410a hcase410b hcase421a hcase400b hcase00 hcase01 hcase04 hcase10 hcase44
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030a hcase030b hcase330a hcase330b hcase321a hcase321b hcase430a hcase430b hcase021a hcase021b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase110a hcase110b hcase410a hcase410b hcase421a hcase401a hcase00 hcase01 hcase04 hcase10 hcase44
                                omega
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase030a hcase030b hcase330b hcase321a hcase430a hcase430b hcase021a hcase340a hcase340b hcase301a hcase110a hcase110b hcase411a hcase400b hcase00 hcase01 hcase04 hcase10 hcase42 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030a hcase030b hcase330a hcase330b hcase321a hcase321b hcase430a hcase430b hcase021a hcase021b hcase340a hcase340b hcase301a hcase301b hcase121a hcase121b hcase110a hcase110b hcase411a hcase401a hcase00 hcase01 hcase04 hcase10 hcase42 hcase44
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase030a hcase030b hcase330a hcase330b hcase321a hcase321b hcase430a hcase430b hcase021a hcase021b hcase340a hcase340b hcase301a hcase301b hcase121a hcase111a hcase00 hcase01 hcase04 hcase10 hcase40 hcase41 hcase42 hcase44
                          omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase030a hcase030b hcase330b hcase321a hcase430a hcase430b hcase021a hcase341a hcase400b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase41 hcase42 hcase44
                      omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030a hcase030b hcase330a hcase330b hcase321a hcase321b hcase430b hcase341a hcase341b hcase401a hcase440b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase41 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030b hcase330a hcase330b hcase321a hcase321b hcase430b hcase021a hcase341a hcase341b hcase401a hcase441a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase41 hcase42
                        omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030a hcase030b hcase330b hcase321a hcase321b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase30 hcase34 hcase40 hcase41 hcase42 hcase44
                omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030b hcase400a hcase400b hcase020b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase030a hcase030b hcase331a hcase400a hcase400b hcase021a hcase320b hcase340b hcase300b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase030a hcase030b hcase331a hcase400b hcase021a hcase320b hcase340a hcase340b hcase301a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase030a hcase030b hcase331a hcase400b hcase021a hcase320b hcase341a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase030a hcase030b hcase331a hcase400a hcase400b hcase021a hcase321a hcase340b hcase300b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase030a hcase030b hcase331a hcase400a hcase400b hcase021a hcase021b hcase321a hcase340a hcase340b hcase301a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase030a hcase030b hcase331a hcase400a hcase400b hcase021a hcase021b hcase321a hcase341a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase41 hcase42 hcase43 hcase44
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
                      clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase311b hcase030b hcase401a hcase410b hcase420b hcase430b hcase020b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase32 hcase34 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030b hcase401a hcase410a hcase410b hcase420a hcase420b hcase430b hcase021a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase32 hcase34 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030a hcase030b hcase331a hcase331b hcase401a hcase410a hcase410b hcase420a hcase420b hcase431a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase30 hcase32 hcase34 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030a hcase030b hcase331a hcase331b hcase401a hcase410a hcase410b hcase421a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase30 hcase32 hcase34 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase030a hcase030b hcase331a hcase331b hcase401a hcase411a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase30 hcase32 hcase34 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase031a hcase020b hcase300b hcase340b hcase320b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase020a hcase020b hcase300b hcase340b hcase321a hcase330b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase031a hcase020a hcase020b hcase300b hcase340b hcase321a hcase331a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase031a hcase020b hcase300a hcase300b hcase341a hcase400b hcase330b hcase320b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase031a hcase020a hcase020b hcase300a hcase300b hcase341a hcase400b hcase330b hcase321a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase031a hcase020b hcase300a hcase300b hcase341a hcase400b hcase331a hcase320b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase031a hcase031b hcase020a hcase020b hcase300a hcase300b hcase341a hcase400a hcase400b hcase331a hcase321a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase031a hcase031b hcase020a hcase020b hcase300a hcase300b hcase401a hcase401b hcase420a hcase420b hcase410a hcase410b hcase430a hcase430b hcase440b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase32 hcase33
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase031a hcase020b hcase300a hcase300b hcase341a hcase341b hcase401a hcase420b hcase410b hcase430b hcase441a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase32 hcase33
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase031a hcase031b hcase020a hcase020b hcase300a hcase300b hcase341a hcase341b hcase401a hcase420a hcase420b hcase410a hcase410b hcase431a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase32 hcase33 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase031a hcase031b hcase020a hcase020b hcase300a hcase300b hcase341a hcase341b hcase401a hcase420a hcase420b hcase411a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase32 hcase33 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase031a hcase031b hcase020a hcase020b hcase300a hcase300b hcase341a hcase341b hcase401a hcase421a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase32 hcase33 hcase41 hcase43 hcase44
                    omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase031a hcase020b hcase301a hcase400b hcase320b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase140a hcase140b hcase131a hcase131b hcase031a hcase020a hcase020b hcase301a hcase400b hcase321a hcase330b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase34 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase131a hcase131b hcase031a hcase031b hcase020a hcase020b hcase301a hcase400a hcase400b hcase321a hcase331a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase34 hcase41 hcase42 hcase43 hcase44
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
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase020a hcase020b hcase301a hcase301b hcase401a hcase410a hcase410b hcase420a hcase420b hcase430b hcase440b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase32 hcase33 hcase34
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase031a hcase020b hcase301a hcase301b hcase401a hcase410b hcase420b hcase430b hcase441a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase32 hcase33 hcase34
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase031a hcase031b hcase020a hcase020b hcase301a hcase301b hcase401a hcase410a hcase410b hcase420a hcase420b hcase431a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase32 hcase33 hcase34 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase031a hcase031b hcase020a hcase020b hcase301a hcase301b hcase401a hcase410a hcase410b hcase421a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase32 hcase33 hcase34 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase031a hcase031b hcase020a hcase020b hcase301a hcase301b hcase401a hcase411a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase32 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase140a hcase140b hcase311a hcase311b hcase131a hcase131b hcase031a hcase021a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
  ·
    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
    ·
      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
      ·
        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
        ·
          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330b hcase300b hcase310b hcase320b hcase020a hcase020b hcase340b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101b hcase010b hcase040b hcase141b hcase030b hcase330b hcase300b hcase310b hcase320b hcase020b hcase341a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase040b hcase030a hcase030b hcase330b hcase300b hcase310b hcase320b hcase021a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase010a hcase010b hcase040a hcase040b hcase030a hcase030b hcase330b hcase300b hcase310b hcase321a hcase340b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase030a hcase030b hcase330b hcase300b hcase310b hcase321a hcase341a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase030a hcase030b hcase330b hcase300b hcase311a hcase020a hcase020b hcase340b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase030b hcase330b hcase300b hcase311a hcase020b hcase341a hcase320b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase030a hcase030b hcase330b hcase300b hcase311a hcase020a hcase020b hcase341a hcase321a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040b hcase030a hcase030b hcase330b hcase300b hcase311a hcase021a hcase320b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase030a hcase030b hcase330b hcase300b hcase311a hcase021a hcase321a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330b hcase301a hcase110a hcase110b hcase120a hcase120b hcase130a hcase130b hcase340b hcase320b hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110b hcase120b hcase130b hcase340a hcase340b hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase040b hcase030a hcase030b hcase330b hcase301a hcase110a hcase110b hcase120a hcase120b hcase130a hcase130b hcase341a hcase320b hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040b hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110b hcase120b hcase130b hcase341a hcase341b hcase320a hcase320b hcase401a hcase430b hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase41 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase120a hcase120b hcase130a hcase130b hcase341a hcase341b hcase320a hcase320b hcase401a hcase431a hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase41 hcase42 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110b hcase120b hcase130b hcase341a hcase341b hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                    ·
                      clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101b hcase010a hcase010b hcase040b hcase141b hcase030b hcase330b hcase301a hcase301b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase420b hcase400b hcase020b hcase00 hcase01 hcase04 hcase10 hcase31 hcase32 hcase34 hcase41 hcase43 hcase44
                      omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase040b hcase030a hcase030b hcase330b hcase301a hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase420a hcase420b hcase400b hcase021a hcase320b hcase00 hcase01 hcase04 hcase10 hcase31 hcase34 hcase41 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase030a hcase030b hcase330b hcase301a hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase420a hcase420b hcase400b hcase021a hcase321a hcase00 hcase01 hcase04 hcase10 hcase31 hcase34 hcase41 hcase43 hcase44
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
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330b hcase301a hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase420a hcase420b hcase401a hcase401b hcase340b hcase410a hcase410b hcase430a hcase430b hcase320b hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase44
                            omega
                          ·
                            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase420b hcase401a hcase340a hcase340b hcase410b hcase430b hcase321a hcase321b hcase020b hcase00 hcase01 hcase04 hcase10 hcase31 hcase44
                              omega
                            ·
                              clear hn4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase030a hcase030b hcase330b hcase301a hcase110a hcase110b hcase120b hcase131a hcase420b hcase401a hcase340b hcase410b hcase430b hcase321a hcase021a hcase00 hcase01 hcase04 hcase10 hcase31 hcase44
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase420a hcase420b hcase401a hcase340a hcase340b hcase410a hcase410b hcase431a hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase32 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase420a hcase420b hcase401a hcase340a hcase340b hcase411a hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase32 hcase43 hcase44
                        omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase420a hcase420b hcase401a hcase401b hcase430a hcase430b hcase020a hcase020b hcase440b hcase00 hcase01 hcase04 hcase10 hcase31 hcase32 hcase41
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase141a hcase141b hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase420a hcase420b hcase401a hcase401b hcase341a hcase341b hcase430a hcase430b hcase020b hcase00 hcase01 hcase04 hcase10 hcase31 hcase32 hcase41
                            omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase420a hcase420b hcase401a hcase341a hcase341b hcase430b hcase440b hcase00 hcase01 hcase04 hcase10 hcase31 hcase32 hcase41
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase141a hcase141b hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase420a hcase420b hcase401a hcase341a hcase341b hcase430b hcase021a hcase441a hcase00 hcase01 hcase04 hcase10 hcase31 hcase32 hcase41
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase420a hcase420b hcase401a hcase341a hcase341b hcase431a hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase32 hcase41 hcase44
                        omega
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase421a hcase430b hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase32 hcase34 hcase41 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase421a hcase430a hcase430b hcase401a hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase32 hcase34 hcase41 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase421a hcase431a hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase32 hcase34 hcase40 hcase41 hcase44
                    omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330b hcase301a hcase110a hcase110b hcase320b hcase340b hcase00 hcase01 hcase02 hcase04 hcase10 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330b hcase301a hcase110a hcase110b hcase320b hcase341a hcase00 hcase01 hcase02 hcase04 hcase10 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase030a hcase030b hcase330a hcase330b hcase301a hcase110a hcase110b hcase321a hcase340a hcase340b hcase420a hcase420b hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase13 hcase31 hcase41 hcase43 hcase44
                      omega
                    ·
                      rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase121a hcase121b hcase321a hcase321b hcase340a hcase340b hcase420b hcase401a hcase020b hcase410b hcase430b hcase00 hcase01 hcase04 hcase10 hcase13 hcase31 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase121a hcase121b hcase321a hcase321b hcase340a hcase340b hcase420a hcase420b hcase401a hcase020a hcase020b hcase410a hcase410b hcase431a hcase00 hcase01 hcase04 hcase10 hcase13 hcase31 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase121a hcase121b hcase321a hcase321b hcase340a hcase340b hcase420a hcase420b hcase401a hcase020a hcase020b hcase411a hcase00 hcase01 hcase04 hcase10 hcase13 hcase31 hcase43 hcase44
                          omega
                      ·
                        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut9 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase030a hcase030b hcase330b hcase301a hcase110b hcase121a hcase321a hcase340b hcase420a hcase420b hcase401a hcase401b hcase130b hcase00 hcase01 hcase04 hcase10 hcase31 hcase41 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase121a hcase321a hcase321b hcase340a hcase340b hcase420a hcase420b hcase401a hcase401b hcase021a hcase021b hcase131a hcase00 hcase01 hcase04 hcase10 hcase31 hcase41 hcase43 hcase44
                          omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase030a hcase030b hcase330b hcase301a hcase110a hcase110b hcase321a hcase340a hcase340b hcase421a hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase13 hcase31 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase121a hcase121b hcase321a hcase321b hcase340a hcase340b hcase421a hcase401a hcase00 hcase01 hcase02 hcase04 hcase10 hcase13 hcase31 hcase41 hcase43 hcase44
                      omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase141a hcase030a hcase030b hcase330b hcase301a hcase110a hcase110b hcase121a hcase321a hcase341a hcase130b hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase030a hcase030b hcase330b hcase301a hcase110a hcase110b hcase121a hcase321a hcase341a hcase130b hcase401a hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase110a hcase110b hcase121a hcase321a hcase321b hcase341a hcase341b hcase131a hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
          ·
            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase141a hcase141b hcase030b hcase330b hcase301a hcase020b hcase130a hcase130b hcase120a hcase120b hcase320b hcase00 hcase01 hcase04 hcase10 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase030a hcase030b hcase330b hcase301a hcase111a hcase020a hcase020b hcase130b hcase120b hcase321a hcase340b hcase00 hcase01 hcase04 hcase10 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase141a hcase030a hcase030b hcase330b hcase301a hcase111a hcase020a hcase020b hcase130b hcase120b hcase321a hcase341a hcase00 hcase01 hcase04 hcase10 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase111a hcase020a hcase020b hcase130a hcase130b hcase121a hcase00 hcase01 hcase04 hcase10 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase111a hcase020a hcase020b hcase131a hcase00 hcase01 hcase04 hcase10 hcase12 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase111a hcase111b hcase130b hcase00 hcase01 hcase04 hcase10 hcase12 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase030a hcase030b hcase330a hcase330b hcase301a hcase301b hcase111a hcase021a hcase021b hcase131a hcase00 hcase01 hcase04 hcase10 hcase12 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
      ·
        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase030a hcase030b hcase331a hcase410b hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase141a hcase141b hcase030b hcase410a hcase410b hcase401a hcase401b hcase020b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase141a hcase141b hcase030b hcase410a hcase410b hcase401a hcase021a hcase430b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase42 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase331a hcase331b hcase410a hcase410b hcase401a hcase021a hcase021b hcase431a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase42 hcase44
                omega
        ·
          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
          ·
            clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase141a hcase141b hcase030b hcase411a hcase411b hcase020b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase40 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040b hcase141a hcase141b hcase030b hcase411a hcase021a hcase430b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase40 hcase42 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase030a hcase030b hcase331a hcase331b hcase411a hcase021a hcase021b hcase431a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase40 hcase42 hcase44
              omega
    ·
      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
      ·
        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase110a hcase110b hcase130b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase320b hcase300b hcase310b hcase330b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase320b hcase300b hcase310b hcase331a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase320b hcase300b hcase311a hcase330b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase320b hcase300b hcase311a hcase331a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase320b hcase301a hcase340b hcase330b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase320b hcase301a hcase340a hcase340b hcase331a hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                        ·
                          clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040a hcase040b hcase141a hcase031a hcase110b hcase131a hcase320a hcase320b hcase301a hcase301b hcase340a hcase340b hcase401a hcase410b hcase430b hcase120b hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase031a hcase031b hcase110a hcase110b hcase131a hcase320a hcase320b hcase301a hcase301b hcase340a hcase340b hcase331a hcase331b hcase401a hcase401b hcase410a hcase410b hcase430a hcase430b hcase121a hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase42 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase320a hcase320b hcase301a hcase301b hcase340a hcase340b hcase331a hcase331b hcase401a hcase410a hcase410b hcase431a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase42 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase320a hcase320b hcase301a hcase301b hcase340a hcase340b hcase331a hcase331b hcase401a hcase411a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase42 hcase43 hcase44
                      omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase320b hcase301a hcase341a hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase33 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase110a hcase110b hcase131a hcase131b hcase320a hcase320b hcase301a hcase301b hcase341a hcase341b hcase401a hcase330a hcase330b hcase410a hcase410b hcase430b hcase440b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase42
                          omega
                        ·
                          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                          ·
                            clear hn4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040a hcase040b hcase141a hcase031a hcase110a hcase110b hcase131a hcase320b hcase301a hcase341a hcase401a hcase330b hcase410b hcase430b hcase441a hcase020b hcase00 hcase01 hcase04 hcase10 hcase12 hcase31 hcase42
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase110a hcase110b hcase131a hcase131b hcase320a hcase320b hcase301a hcase301b hcase341a hcase341b hcase401a hcase401b hcase330a hcase330b hcase410a hcase410b hcase430a hcase430b hcase441a hcase441b hcase021a hcase00 hcase01 hcase04 hcase10 hcase12 hcase31 hcase42
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase320a hcase320b hcase301a hcase301b hcase341a hcase341b hcase401a hcase330a hcase330b hcase410a hcase410b hcase431a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase42 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase320a hcase320b hcase301a hcase301b hcase341a hcase341b hcase401a hcase330a hcase330b hcase411a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                        ·
                          clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase040a hcase040b hcase141a hcase031a hcase110b hcase131a hcase320a hcase320b hcase301a hcase301b hcase341a hcase341b hcase401a hcase430b hcase410b hcase120b hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase031a hcase031b hcase110a hcase110b hcase131a hcase320a hcase320b hcase301a hcase301b hcase341a hcase341b hcase401a hcase401b hcase331a hcase331b hcase430a hcase430b hcase410a hcase410b hcase121a hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase42 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase320a hcase320b hcase301a hcase301b hcase341a hcase341b hcase401a hcase331a hcase331b hcase430a hcase430b hcase411a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase42 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase320a hcase320b hcase301a hcase301b hcase341a hcase341b hcase401a hcase331a hcase331b hcase431a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase41 hcase42 hcase44
                      omega
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase321a hcase330b hcase300b hcase310b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase321a hcase330b hcase300b hcase311a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase010a hcase010b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase321a hcase330b hcase301a hcase340b hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                          ·
                            clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase031a hcase110b hcase131a hcase330a hcase330b hcase301a hcase301b hcase340a hcase340b hcase401a hcase410b hcase420b hcase430b hcase120b hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase031a hcase031b hcase110a hcase110b hcase131a hcase321a hcase321b hcase330a hcase330b hcase301a hcase301b hcase340a hcase340b hcase401a hcase401b hcase410a hcase410b hcase420a hcase420b hcase430a hcase430b hcase121a hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase321a hcase321b hcase330a hcase330b hcase301a hcase301b hcase340a hcase340b hcase401a hcase410a hcase410b hcase420a hcase420b hcase431a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase321a hcase321b hcase330a hcase330b hcase301a hcase301b hcase340a hcase340b hcase401a hcase410a hcase410b hcase421a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase321a hcase321b hcase330a hcase330b hcase301a hcase301b hcase340a hcase340b hcase401a hcase411a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase330a hcase330b hcase301a hcase301b hcase341a hcase341b hcase420b hcase430b hcase410b hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase44
                          omega
                        ·
                          rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                          ·
                            clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase031a hcase110b hcase131a hcase330a hcase330b hcase301a hcase301b hcase341a hcase341b hcase420b hcase430b hcase410b hcase401a hcase120b hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase031a hcase031b hcase110a hcase110b hcase131a hcase321a hcase321b hcase330a hcase330b hcase301a hcase301b hcase341a hcase341b hcase420a hcase420b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase121a hcase00 hcase01 hcase02 hcase04 hcase10 hcase31 hcase44
                            omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase110a hcase110b hcase131a hcase131b hcase321a hcase321b hcase330a hcase330b hcase301a hcase301b hcase341a hcase341b hcase420a hcase420b hcase430b hcase411a hcase440b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase40
                          omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase321a hcase330a hcase330b hcase301a hcase341a hcase420a hcase420b hcase430a hcase430b hcase411a hcase441a hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase321a hcase321b hcase330a hcase330b hcase301a hcase301b hcase341a hcase341b hcase420a hcase420b hcase430a hcase430b hcase411a hcase441a hcase441b hcase401a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31
                            omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase321a hcase321b hcase330b hcase301a hcase301b hcase341a hcase341b hcase420a hcase420b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase40 hcase41 hcase44
                      omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase321a hcase330a hcase330b hcase301a hcase341a hcase421a hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase321a hcase321b hcase330a hcase330b hcase301a hcase301b hcase341a hcase341b hcase421a hcase401a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase41 hcase43 hcase44
                      omega
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase321a hcase331a hcase340b hcase300b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase340a hcase340b hcase301a hcase301b hcase410b hcase420b hcase430b hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase44
                          omega
                        ·
                          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase110a hcase110b hcase131a hcase321a hcase321b hcase340a hcase340b hcase301a hcase301b hcase410b hcase420b hcase430b hcase401a hcase020b hcase00 hcase01 hcase04 hcase10 hcase12 hcase31 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase110a hcase110b hcase131a hcase131b hcase321a hcase321b hcase331a hcase331b hcase340a hcase340b hcase301a hcase301b hcase410a hcase410b hcase420a hcase420b hcase430a hcase430b hcase401a hcase401b hcase021a hcase00 hcase01 hcase04 hcase10 hcase12 hcase31 hcase44
                            omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase331a hcase340a hcase340b hcase301a hcase301b hcase410b hcase420b hcase431a hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase321a hcase321b hcase331a hcase331b hcase340a hcase340b hcase301a hcase301b hcase410a hcase410b hcase420a hcase420b hcase431a hcase401a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase44
                          omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase321a hcase321b hcase331a hcase340a hcase340b hcase301a hcase301b hcase410b hcase421a hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase321a hcase321b hcase331a hcase331b hcase340a hcase340b hcase301a hcase301b hcase410a hcase410b hcase421a hcase401a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase43 hcase44
                        omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase321a hcase331a hcase340a hcase340b hcase301a hcase411a hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase321a hcase321b hcase331a hcase331b hcase340a hcase340b hcase301a hcase301b hcase411a hcase401a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase42 hcase43 hcase44
                      omega
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase040b hcase031a hcase110a hcase110b hcase131a hcase131b hcase321a hcase331a hcase341a hcase300b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase031a hcase031b hcase110a hcase110b hcase131a hcase131b hcase321a hcase331a hcase341a hcase301a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
      ·
        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase040a hcase040b hcase141a hcase141b hcase111a hcase111b hcase130b hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase040a hcase040b hcase141a hcase031a hcase031b hcase111a hcase131a hcase00 hcase01 hcase02 hcase04 hcase10 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega

#print axioms symbolic_v2_mask95_integer_shard002
end Jsp404.SixExactFloorKernel
