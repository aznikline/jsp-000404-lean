import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask95_integer_shard003 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
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
    (hcase041a : 1 ≤ s04)
    (hcase041b : u04 = 1)
    : False := by
  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
  ·
    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
    ·
      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase130a hcase130b hcase020a hcase020b hcase140b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
      ·
        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
        ·
          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase130a hcase130b hcase020a hcase020b hcase141a hcase340b hcase330b hcase320b hcase300b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase340b hcase330b hcase320b hcase301a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase130a hcase130b hcase020a hcase020b hcase141a hcase340b hcase330b hcase321a hcase110a hcase110b hcase300b hcase00 hcase01 hcase03 hcase04 hcase10 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase041a hcase041b hcase130b hcase020a hcase020b hcase141a hcase340a hcase340b hcase330a hcase330b hcase110b hcase301a hcase301b hcase120b hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut9 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase041a hcase041b hcase130b hcase020a hcase020b hcase141a hcase340b hcase330b hcase321a hcase110b hcase301a hcase121a hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase041a hcase041b hcase130b hcase020a hcase020b hcase141a hcase340b hcase330b hcase321a hcase111a hcase120b hcase00 hcase01 hcase03 hcase04 hcase10 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase340a hcase340b hcase330a hcase330b hcase321a hcase321b hcase111a hcase121a hcase00 hcase01 hcase03 hcase04 hcase10 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase041a hcase130b hcase020a hcase020b hcase141a hcase340a hcase340b hcase400b hcase430b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase41 hcase42 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase041a hcase130b hcase020a hcase020b hcase141a hcase340a hcase340b hcase331a hcase400b hcase431a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase41 hcase42 hcase44
                omega
            ·
              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase130b hcase020a hcase020b hcase141a hcase340a hcase340b hcase331a hcase331b hcase401a hcase440b hcase430b hcase420b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase41
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase340a hcase340b hcase331a hcase331b hcase401a hcase440a hcase440b hcase430a hcase430b hcase421a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase41
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase340a hcase340b hcase331a hcase331b hcase401a hcase440a hcase440b hcase431a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase41 hcase42
                  omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut86 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase041a hcase130b hcase020b hcase141a hcase340a hcase340b hcase401a hcase441a hcase430b hcase420b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase41
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase340a hcase340b hcase331a hcase331b hcase401a hcase441a hcase441b hcase430a hcase430b hcase421a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase41
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase340a hcase340b hcase331a hcase331b hcase401a hcase441a hcase441b hcase431a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase41 hcase42
                  omega
        ·
          rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
          ·
            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase041a hcase130b hcase020a hcase020b hcase141a hcase341a hcase341b hcase120a hcase120b hcase430b hcase110a hcase110b hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase30 hcase31 hcase32 hcase33 hcase41 hcase42 hcase44
                  omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase130b hcase020a hcase020b hcase141a hcase341a hcase341b hcase120b hcase430b hcase110b hcase401a hcase440b hcase00 hcase01 hcase03 hcase04 hcase10 hcase30 hcase31 hcase32 hcase33 hcase41 hcase42
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase041a hcase130b hcase020a hcase020b hcase141a hcase341a hcase341b hcase120b hcase430b hcase110b hcase401a hcase441a hcase00 hcase01 hcase03 hcase04 hcase10 hcase30 hcase31 hcase32 hcase33 hcase41 hcase42
                    omega
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase041a hcase130b hcase020b hcase141a hcase341a hcase120a hcase120b hcase430a hcase430b hcase300b hcase320b hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase33 hcase40 hcase41 hcase42 hcase44
                    omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase041a hcase130b hcase020a hcase020b hcase141a hcase341a hcase120b hcase430a hcase430b hcase111a hcase300b hcase321a hcase330b hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase40 hcase41 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase041a hcase130b hcase020a hcase020b hcase141a hcase341a hcase120b hcase430a hcase430b hcase111a hcase300b hcase321a hcase331a hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase40 hcase41 hcase42 hcase44
                      omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase041a hcase130b hcase020a hcase020b hcase141a hcase341a hcase341b hcase120b hcase430b hcase111a hcase301a hcase301b hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase32 hcase33 hcase41 hcase42 hcase44
                    omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase120a hcase120b hcase430a hcase430b hcase301a hcase401a hcase401b hcase330b hcase320b hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase41 hcase42 hcase44
                        omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase130b hcase020a hcase020b hcase141a hcase341a hcase120a hcase120b hcase430a hcase430b hcase111a hcase301a hcase401a hcase330b hcase321a hcase440b hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase41 hcase42
                          omega
                        ·
                          clear hn4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase041a hcase130b hcase020a hcase020b hcase141a hcase341a hcase120a hcase120b hcase430a hcase430b hcase111a hcase301a hcase401a hcase330b hcase321a hcase441a hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase41 hcase42
                          omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut86 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase041a hcase130b hcase020b hcase141a hcase341a hcase341b hcase120a hcase120b hcase430b hcase111a hcase111b hcase301a hcase301b hcase401a hcase420b hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase32 hcase41 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase341b hcase120a hcase120b hcase430a hcase430b hcase111a hcase111b hcase301a hcase301b hcase401a hcase331a hcase331b hcase421a hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase32 hcase41 hcase44
                        omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase341b hcase120a hcase120b hcase110a hcase110b hcase320a hcase320b hcase330b hcase00 hcase01 hcase03 hcase04 hcase10 hcase30 hcase31 hcase40 hcase41 hcase42 hcase44
                    omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase120a hcase120b hcase431a hcase431b hcase110a hcase110b hcase320a hcase320b hcase331a hcase331b hcase440b hcase00 hcase01 hcase03 hcase04 hcase10 hcase30 hcase31 hcase40 hcase41 hcase42
                      omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010b hcase041a hcase130a hcase130b hcase020a hcase020b hcase141a hcase341a hcase120a hcase120b hcase431a hcase110a hcase110b hcase320b hcase331a hcase441a hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase30 hcase31 hcase41 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase341b hcase120a hcase120b hcase431a hcase110a hcase110b hcase320a hcase320b hcase331a hcase331b hcase441a hcase441b hcase401a hcase00 hcase01 hcase03 hcase04 hcase10 hcase30 hcase31 hcase41 hcase42
                        omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase041a hcase041b hcase130b hcase020a hcase020b hcase141a hcase341a hcase341b hcase120b hcase431a hcase431b hcase110b hcase00 hcase01 hcase03 hcase04 hcase10 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase44
                  omega
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase341b hcase120a hcase120b hcase111a hcase111b hcase300a hcase300b hcase330b hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase32 hcase40 hcase41 hcase42 hcase44
                    omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010b hcase041a hcase130b hcase020a hcase020b hcase141a hcase341a hcase120b hcase431a hcase431b hcase111a hcase300b hcase331a hcase320b hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase40 hcase41 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase041a hcase130b hcase020a hcase020b hcase141a hcase341a hcase120b hcase431a hcase431b hcase111a hcase300b hcase331a hcase321a hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase40 hcase41 hcase42 hcase44
                      omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase041a hcase130b hcase020a hcase020b hcase141a hcase341a hcase120a hcase120b hcase431a hcase301a hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase32 hcase33 hcase41 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase341b hcase120a hcase120b hcase431a hcase111a hcase111b hcase301a hcase301b hcase401a hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase32 hcase33 hcase41 hcase42 hcase44
                    omega
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hn4 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101b hcase010b hcase041a hcase130a hcase130b hcase020b hcase141a hcase141b hcase341a hcase121b hcase330b hcase310b hcase320b hcase300b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase330b hcase310a hcase310b hcase320b hcase301a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase041a hcase130a hcase130b hcase020a hcase020b hcase141a hcase341a hcase330b hcase310a hcase310b hcase321a hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase30 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase130b hcase020a hcase020b hcase141a hcase341a hcase121a hcase330b hcase310a hcase310b hcase321a hcase401a hcase440b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase30 hcase41 hcase42 hcase43
                      omega
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase041a hcase130a hcase130b hcase020a hcase020b hcase141a hcase341a hcase121a hcase121b hcase330b hcase310b hcase321a hcase401a hcase401b hcase441a hcase300b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase41 hcase42 hcase43
                        omega
                      ·
                        clear hn4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase041a hcase130b hcase020a hcase020b hcase141a hcase341a hcase121a hcase330b hcase310a hcase310b hcase321a hcase401a hcase441a hcase301a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase41 hcase42 hcase43
                        omega
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase330b hcase311a hcase300a hcase300b hcase320b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase130b hcase020a hcase020b hcase141a hcase341a hcase121a hcase330b hcase311a hcase300a hcase300b hcase321a hcase440b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut14 hcut82 hcut71 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase041a hcase130a hcase130b hcase020a hcase020b hcase141a hcase341a hcase121a hcase121b hcase330b hcase311a hcase300b hcase321a hcase441a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43
                      omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase330b hcase311a hcase301a hcase320b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase121a hcase121b hcase330a hcase330b hcase311a hcase301a hcase321a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101b hcase010b hcase041a hcase130a hcase130b hcase020b hcase141a hcase141b hcase341a hcase121b hcase331a hcase300b hcase320b hcase310b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase041a hcase130b hcase020b hcase141a hcase341a hcase121a hcase121b hcase331a hcase300b hcase320b hcase311a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase341b hcase121a hcase121b hcase300a hcase300b hcase321a hcase321b hcase430b hcase420b hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase31 hcase41 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut86 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase041a hcase130b hcase020b hcase141a hcase341a hcase341b hcase121a hcase121b hcase300a hcase300b hcase321a hcase321b hcase430b hcase420b hcase401a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase31 hcase41 hcase44
                        omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase010a hcase010b hcase041a hcase130b hcase020a hcase020b hcase141a hcase341a hcase121a hcase331a hcase300b hcase321a hcase430a hcase430b hcase110b hcase310b hcase00 hcase01 hcase03 hcase04 hcase10 hcase40 hcase41 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase121a hcase121b hcase331a hcase300a hcase300b hcase321a hcase430a hcase430b hcase421a hcase421b hcase110a hcase110b hcase311a hcase00 hcase01 hcase03 hcase04 hcase10 hcase40 hcase41 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase341a hcase341b hcase121a hcase331a hcase331b hcase300a hcase300b hcase321a hcase321b hcase430a hcase430b hcase421a hcase421b hcase111a hcase00 hcase01 hcase03 hcase04 hcase10 hcase31 hcase40 hcase41 hcase44
                        omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase041a hcase130a hcase130b hcase020a hcase020b hcase141a hcase341a hcase331a hcase300a hcase300b hcase321a hcase431a hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase31 hcase41 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase341b hcase121a hcase121b hcase331a hcase331b hcase300a hcase300b hcase321a hcase321b hcase431a hcase401a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase31 hcase41 hcase42 hcase44
                      omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase331a hcase301a hcase320b hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase31 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hcut11 hcut9 hcut40 hcut18 hcut22 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut1 hcut68 hcut39 hcut86 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase041a hcase130b hcase020b hcase141a hcase341a hcase331a hcase301a hcase320b hcase401a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase31 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase130a hcase130b hcase020a hcase020b hcase141a hcase141b hcase341a hcase121a hcase121b hcase331a hcase301a hcase321a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase130a hcase130b hcase021a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega
  ·
    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
    ·
      rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
      ·
        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase131a hcase131b hcase030a hcase030b hcase020a hcase020b hcase140b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101b hcase010a hcase010b hcase041a hcase131b hcase030b hcase020b hcase141a hcase141b hcase400b hcase420b hcase410b hcase330b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101b hcase010a hcase010b hcase041a hcase131b hcase030b hcase020b hcase141a hcase141b hcase400b hcase420b hcase410b hcase331a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101b hcase010a hcase010b hcase041a hcase131a hcase131b hcase030b hcase020b hcase141a hcase141b hcase400b hcase420b hcase411a hcase330b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101b hcase010a hcase010b hcase041a hcase131a hcase131b hcase030b hcase020b hcase141a hcase141b hcase400b hcase420b hcase411a hcase331a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase041a hcase131a hcase131b hcase030a hcase030b hcase020a hcase020b hcase141a hcase400b hcase421a hcase330b hcase410b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase131a hcase131b hcase030a hcase030b hcase020a hcase020b hcase141a hcase141b hcase400a hcase400b hcase421a hcase330a hcase330b hcase411a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut0 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase010a hcase010b hcase041a hcase131a hcase131b hcase030a hcase030b hcase020a hcase020b hcase141a hcase400b hcase421a hcase331a hcase410b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase131a hcase131b hcase030a hcase030b hcase020a hcase020b hcase141a hcase141b hcase400a hcase400b hcase421a hcase331a hcase331b hcase411a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
          ·
            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase101a hcase101b hcase010b hcase041a hcase030b hcase020b hcase141a hcase141b hcase401a hcase430b hcase410b hcase420b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase131a hcase131b hcase030a hcase030b hcase020a hcase020b hcase141a hcase141b hcase401a hcase430a hcase430b hcase410a hcase410b hcase421a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase131a hcase131b hcase030a hcase030b hcase020a hcase020b hcase141a hcase141b hcase401a hcase430a hcase430b hcase411a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase041b hcase131a hcase131b hcase030a hcase030b hcase020a hcase020b hcase141a hcase141b hcase401a hcase431a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase44
              omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase131a hcase131b hcase030a hcase030b hcase021a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut11 hcut9 hcut40 hcut18 hcut22 hcut81 hcut0 hcut10 hcut32 hcut13 hcut30 hcut52 hcut14 hcut82 hcut71 hcut91 hcut45 hcut61 hcut63 hcut23 hcut47 hcut2 hcut37 hcut1 hcut68 hcut39 hcut86 hcut15 hcut46 hcut59 hcut20 hcut35 hcut89 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase101a hcase101b hcase010a hcase010b hcase041a hcase131a hcase131b hcase031a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega

#print axioms symbolic_v2_mask95_integer_shard003
end Jsp404.SixExactFloorKernel
