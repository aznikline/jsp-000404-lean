import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_mask575_integer_shard005 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut20 : (s34 + s40 + s43 + u34 + u40 + u43) + 1 ≤ (n + 1))
    (hcut26 : (s10 + s11 + s13 + s31 + s40 + s43 + u10 + u11 + u13 + u31 + u40 + u43) + 1 ≤ (2 * n + 1))
    (hcut52 : (s01 + s30 + s42 + u01 + u30 + u42 + 1) + 1 ≤ (n))
    (hcut2 : (s40 + s41 + s42 + s43 + s44 + u40 + u41 + u42 + u43 + u44) + 1 ≤ (n + 1))
    (hcut81 : (s01 + s02 + s03 + s04 + u01 + u02 + u03 + u04 + 1) + 1 ≤ (n))
    (hcut82 : (s32 + s34 + s40 + u32 + u34 + u40) + 1 ≤ (n + 1))
    (hcut42 : (s14 + u14) + 1 ≤ (s34 + 2))
    (hcut72 : (s14 + s33 + u14 + u33 + 2) + 1 ≤ (n))
    (hcut13 : (s33 + s40 + u33 + u40 + 1) + 1 ≤ (n))
    (hcut73 : (s01 + s30 + s34 + s42 + u01 + u30 + u34 + u42) + 1 ≤ (n))
    (hcut23 : (s10 + s13 + s31 + s40 + s43 + u10 + u13 + u31 + u40 + u43) + 1 ≤ (2 * n))
    (hcut103 : (s00 + s01 + s02 + s03 + s04 + u00 + u01 + u02 + u03 + u04) + 1 ≤ (n + 1))
    (hcut33 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 2))
    (hcut3 : (s41 + u41) + 1 ≤ (s31 + 2))
    (hcut90 : (s02 + s03 + s12 + s30 + s32 + u02 + u03 + u12 + u30 + u32) + 1 ≤ (n))
    (hcut87 : (s02 + s03 + u02 + u03 + 3) + 1 ≤ (n))
    (hcut65 : (s30 + s31 + s33 + s34 + u30 + u31 + u33 + u34) + 1 ≤ (n))
    (hcut14 : (s30 + s43 + u30 + u43 + 1) + 1 ≤ (n))
    (hcut91 : (s02 + s03 + s11 + s32 + s33 + u02 + u03 + u11 + u32 + u33 + 2) + 1 ≤ (n))
    (hcut84 : (s34 + s40 + u34 + u40) + 1 ≤ (n))
    (hcut43 : (s30 + s31 + u30 + u31 + 2) + 1 ≤ (n))
    (hcut31 : (s12 + s30 + u12 + u30) + 1 ≤ (s40 + 3))
    (hcut7 : (s42 + u42) + 1 ≤ (s32 + 2))
    (hcut8 : (s11 + s34 + s43 + u11 + u34 + u43) + 1 ≤ (n))
    (hcut86 : (s02 + s03 + s31 + s32 + s33 + u02 + u03 + u31 + u32 + u33 + 1) + 1 ≤ (n))
    (hcut69 : (s00 + s04 + s13 + s40 + s44 + u00 + u04 + u13 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut18 : (s02 + u02) + 1 ≤ (s34 + 1))
    (hcut77 : (s03 + s14 + s31 + s32 + u03 + u14 + u31 + u32 + 1) + 1 ≤ (n))
    (hcut1 : (s40 + s41 + u40 + u41) + 1 ≤ (s30 + s31 + 4))
    (hcut4 : (s14 + s31 + s43 + u14 + u31 + u43) + 1 ≤ (n))
    (hcut71 : (s03 + s10 + s11 + s14 + u03 + u10 + u11 + u14 + 2) + 1 ≤ (n))
    (hcut45 : (s01 + s30 + s31 + u01 + u30 + u31) + 1 ≤ (n))
    (hcut36 : (s03 + s32 + s33 + u03 + u32 + u33) + 1 ≤ (s13 + 2))
    (hcut66 : (s01 + s30 + s31 + s34 + u01 + u30 + u31 + u34) + 1 ≤ (n + 1))
    (hcut53 : (s30 + s43 + s44 + u30 + u43 + u44) + 1 ≤ (n + 1))
    (hcut41 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut39 : (s01 + s31 + s34 + s43 + u01 + u31 + u34 + u43) + 1 ≤ (n + 1))
    (hcut15 : (s32 + s33 + s40 + u32 + u33 + u40) + 1 ≤ (n))
    (hcut12 : (s42 + s43 + u42 + u43 + 1) + 1 ≤ (n))
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
    (hcase131a : 1 ≤ s13)
    (hcase131b : u13 = 1)
    (hcase010a : s01 = 0)
    (hcase010b : u01 = 0)
    (hcase030a : s03 = 0)
    (hcase030b : u03 = 0)
    (hcase111a : 1 ≤ s11)
    (hcase111b : u11 = 1)
    (hcase041a : 1 ≤ s04)
    (hcase041b : u04 = 1)
    : False := by
  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
  ·
    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase020a hcase020b hcase140b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega
    ·
      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
      ·
        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
        ·
          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase020a hcase020b hcase141a hcase420a hcase420b hcase430a hcase430b hcase440a hcase440b hcase310a hcase310b hcase340b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase40 hcase41
                omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase020a hcase020b hcase141a hcase420b hcase430b hcase440b hcase310b hcase341a hcase341b hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase41
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut90 hcut87 hcut65 hcut14 hcut91 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase420b hcase430b hcase440b hcase310b hcase401a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase41
                  omega
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase020a hcase020b hcase141a hcase420a hcase420b hcase430a hcase430b hcase440a hcase440b hcase311a hcase311b hcase340b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase40 hcase41
                omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase420b hcase430b hcase440b hcase311a hcase311b hcase341b hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase41
                  omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase020a hcase020b hcase141a hcase420b hcase430b hcase440b hcase311a hcase341a hcase341b hcase401a hcase300b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase32 hcase33 hcase41
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase420b hcase430b hcase440b hcase311a hcase401a hcase301a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase32 hcase33 hcase41
                    omega
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase010b hcase030a hcase030b hcase041a hcase020b hcase141a hcase420b hcase430b hcase441a hcase410b hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase010b hcase030b hcase111a hcase111b hcase041a hcase020b hcase141a hcase141b hcase420b hcase430b hcase441a hcase410b hcase401a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34
                omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase010b hcase030a hcase030b hcase041a hcase020b hcase141a hcase420b hcase430b hcase441a hcase411a hcase400b hcase310b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase34
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase020b hcase141a hcase420b hcase430b hcase441a hcase411a hcase400b hcase311a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase34
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase420a hcase420b hcase430a hcase430b hcase441a hcase411a hcase401a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34
                omega
        ·
          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
          ·
            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase020a hcase020b hcase141a hcase420a hcase420b hcase431a hcase431b hcase310a hcase310b hcase340b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase40 hcase41 hcase44
              omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut72 hcut13 hcut73 hcut23 hcut103 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase010b hcase030b hcase041a hcase020b hcase141a hcase420b hcase431a hcase310a hcase310b hcase341a hcase410b hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase44
                  omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase420b hcase431a hcase310a hcase310b hcase410b hcase401a hcase440b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase420a hcase420b hcase431a hcase310a hcase310b hcase341a hcase341b hcase410a hcase410b hcase401a hcase441a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase420a hcase420b hcase431a hcase431b hcase310b hcase341a hcase341b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase40 hcase44
                omega
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut71 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase010b hcase030b hcase111a hcase111b hcase041a hcase020b hcase141a hcase420b hcase431a hcase410b hcase400b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase34 hcase44
                omega
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase020a hcase020b hcase141a hcase420a hcase420b hcase431a hcase431b hcase311a hcase311b hcase410a hcase410b hcase401a hcase401b hcase340b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase44
                  omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase420b hcase431a hcase311a hcase311b hcase410b hcase401a hcase440b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase420a hcase420b hcase431a hcase311a hcase311b hcase410a hcase410b hcase401a hcase341a hcase341b hcase441a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33
                    omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut71 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase020a hcase020b hcase141a hcase420b hcase431a hcase311a hcase411a hcase400b hcase440b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase34
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase420a hcase420b hcase431a hcase311a hcase311b hcase411a hcase400a hcase400b hcase441a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase34
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase420a hcase420b hcase431a hcase311a hcase311b hcase411a hcase401a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase34 hcase44
                omega
      ·
        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
        ·
          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
          ·
            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase010b hcase030a hcase030b hcase041a hcase020b hcase141a hcase421a hcase400b hcase410b hcase430b hcase320b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase44
                omega
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut84 hcut43 hcut31 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase421a hcase400b hcase410b hcase430b hcase321a hcase440b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut8 hcut86 hcut69 hcut18 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase020b hcase141a hcase421a hcase400b hcase410b hcase430b hcase321a hcase441a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34
                  omega
            ·
              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase421a hcase400b hcase410b hcase431a hcase440b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase421a hcase400a hcase400b hcase410a hcase410b hcase431a hcase441a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34
                omega
          ·
            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase421a hcase421b hcase400a hcase400b hcase430a hcase430b hcase310b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase33 hcase34 hcase44
                omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase400a hcase400b hcase411a hcase411b hcase430a hcase430b hcase311a hcase311b hcase320b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33 hcase34 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut8 hcut86 hcut69 hcut18 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase020b hcase141a hcase421a hcase400b hcase411a hcase430b hcase311a hcase321a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase33 hcase34 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase421a hcase400a hcase400b hcase411a hcase431a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
              omega
        ·
          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase020a hcase020b hcase141a hcase421a hcase421b hcase401a hcase401b hcase340b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase41 hcase43 hcase44
            omega
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut2 hcut81 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase020a hcase020b hcase141a hcase421a hcase401a hcase341a hcase410b hcase430b hcase440b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase421a hcase401a hcase341a hcase341b hcase410a hcase410b hcase430a hcase430b hcase441a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase421a hcase401a hcase341a hcase341b hcase410a hcase410b hcase431a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut20 hcut26 hcut52 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut103 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase421a hcase401a hcase341a hcase341b hcase411a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase43 hcase44
              omega
  ·
    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut20 hcut26 hcut52 hcut2 hcut81 hcut82 hcut42 hcut72 hcut13 hcut73 hcut23 hcut33 hcut3 hcut90 hcut87 hcut65 hcut14 hcut91 hcut84 hcut43 hcut31 hcut7 hcut8 hcut86 hcut69 hcut18 hcut77 hcut1 hcut4 hcut71 hcut45 hcut36 hcut66 hcut53 hcut41 hcut39 hcut15 hcut12 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase010a hcase010b hcase030a hcase030b hcase111a hcase111b hcase041a hcase021a hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
    omega

#print axioms symbolic_mask575_integer_shard005
end Jsp404.SixExactFloorKernel
