import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_mask567_integer_shard002 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut9 : (s04 + s32 + u04 + u32 + 1) + 1 ≤ (n))
    (hcut64 : (s30 + s31 + s32 + s33 + u30 + u31 + u32 + u33) + 1 ≤ (n))
    (hcut40 : (s01 + s34 + u01 + u34) + 1 ≤ (s44 + 1))
    (hcut25 : (s33 + u33 + 2) + 1 ≤ (n))
    (hcut1 : (s32 + s33 + s34 + s40 + s41 + u32 + u33 + u34 + u40 + u41) + 1 ≤ (n + 1))
    (hcut17 : (s03 + s31 + s32 + u03 + u31 + u32) + 1 ≤ (n))
    (hcut14 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut28 : (s03 + s04 + u03 + u04 + 2) + 1 ≤ (n))
    (hcut12 : (s32 + u32 + 2) + 1 ≤ (n))
    (hcut36 : (s01 + s30 + s33 + s34 + u01 + u30 + u33 + u34) + 1 ≤ (n))
    (hcut2 : (s00 + s04 + s13 + s40 + s44 + u00 + u04 + u13 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut49 : (s03 + s11 + s31 + u03 + u11 + u31 + 2) + 1 ≤ (n))
    (hcut53 : (s30 + s31 + s33 + s34 + u30 + u31 + u33 + u34) + 1 ≤ (n))
    (hcut61 : (s11 + s14 + s31 + s32 + u11 + u14 + u31 + u32) + 1 ≤ (n))
    (hcut4 : (s03 + s32 + s41 + u03 + u32 + u41) + 1 ≤ (s13 + 2))
    (hcut16 : (s30 + s43 + u30 + u43 + 2) + 1 ≤ (n))
    (hcut10 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 2))
    (hcut48 : (s30 + s31 + s34 + u30 + u31 + u34 + 1) + 1 ≤ (n))
    (hcut32 : (s02 + s42 + u02 + u42) + 1 ≤ (s32 + 1))
    (hcut18 : (s30 + s31 + s43 + s44 + u30 + u31 + u43 + u44) + 1 ≤ (n + 2))
    (hcut55 : (s11 + s31 + s32 + u11 + u31 + u32 + 1) + 1 ≤ (n))
    (hcut67 : (s01 + s02 + s42 + s43 + u01 + u02 + u42 + u43) + 1 ≤ (s32 + 2))
    (hcut66 : (s40 + s42 + s43 + s44 + u40 + u42 + u43 + u44) + 1 ≤ (n + 1))
    (hcut52 : (s30 + s31 + s33 + u30 + u31 + u33 + 1) + 1 ≤ (n))
    (hcut59 : (s30 + s32 + s33 + u30 + u32 + u33 + 1) + 1 ≤ (n))
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
    (hcase041a : 1 ≤ s04)
    (hcase041b : u04 = 1)
    : False := by
  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
  ·
    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase020a hcase020b hcase140b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega
    ·
      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
      ·
        rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase300b hcase310b hcase330b hcase340b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase300b hcase310b hcase330b hcase341a hcase440b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase300b hcase310b hcase330b hcase341a hcase441a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43
                    omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase300a hcase300b hcase310a hcase310b hcase331a hcase331b hcase410b hcase400b hcase430b hcase440b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase34 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase320b hcase010b hcase300a hcase300b hcase310a hcase310b hcase331a hcase331b hcase410b hcase400b hcase430b hcase441a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase34 hcase42
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase300a hcase300b hcase310a hcase310b hcase331a hcase331b hcase410a hcase410b hcase400a hcase400b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase34 hcase42 hcase44
                      omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase300b hcase310b hcase331a hcase410a hcase410b hcase401a hcase401b hcase340b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320a hcase320b hcase010a hcase010b hcase300b hcase310b hcase331a hcase410a hcase410b hcase341a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase300b hcase310b hcase331a hcase411a hcase411b hcase340b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320a hcase320b hcase010a hcase010b hcase300b hcase310b hcase331a hcase341a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase42 hcase43 hcase44
                    omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase300b hcase311a hcase330b hcase340b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase300a hcase300b hcase311a hcase330b hcase341a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase300a hcase300b hcase311a hcase331a hcase340b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase300a hcase300b hcase311a hcase331a hcase341a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase301a hcase310b hcase330b hcase340b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase301a hcase310a hcase310b hcase330b hcase341a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase301a hcase310a hcase310b hcase331a hcase340b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase301a hcase310b hcase331a hcase341a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase301a hcase311a hcase330b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase010a hcase010b hcase301a hcase311a hcase331a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase320b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase130b hcase00 hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
          ·
            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase020a hcase020b hcase141a hcase321a hcase131a hcase131b hcase010a hcase010b hcase340b hcase330b hcase300b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase340b hcase330a hcase330b hcase301a hcase310b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase340b hcase330a hcase330b hcase301a hcase311a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase340b hcase331a hcase310b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase340b hcase331a hcase311a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase131a hcase131b hcase010b hcase341a hcase341b hcase430b hcase420b hcase030b hcase400b hcase410b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase131a hcase131b hcase010b hcase341a hcase341b hcase430b hcase420b hcase030a hcase030b hcase400b hcase411a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase44
                        omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase321b hcase131a hcase131b hcase010a hcase010b hcase430a hcase430b hcase420a hcase420b hcase030a hcase030b hcase401a hcase401b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase41
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase131a hcase010b hcase341a hcase341b hcase430b hcase420b hcase030a hcase030b hcase401a hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase41
                        omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase131a hcase131b hcase010b hcase341a hcase341b hcase430b hcase420b hcase031a hcase400b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase41 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase131a hcase010b hcase341a hcase341b hcase430b hcase420b hcase031a hcase401a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase41 hcase44
                      omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010b hcase341a hcase341b hcase430b hcase421a hcase400b hcase030b hcase410b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010b hcase341a hcase341b hcase430b hcase421a hcase400b hcase030a hcase030b hcase411a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010b hcase341a hcase341b hcase430b hcase421a hcase400b hcase031a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase41 hcase44
                      omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase430b hcase421a hcase401a hcase440b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase41
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase010b hcase341a hcase341b hcase430b hcase421a hcase401a hcase441a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase41
                      omega
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase431a hcase431b hcase030a hcase030b hcase410a hcase410b hcase420a hcase420b hcase300b hcase310b hcase330b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase40
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat4 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase431a hcase431b hcase030b hcase410a hcase410b hcase420a hcase420b hcase300b hcase310b hcase330b hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase40
                              omega
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase431a hcase030a hcase030b hcase410a hcase410b hcase420a hcase420b hcase300b hcase310b hcase331a hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase40
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase431a hcase030b hcase410a hcase410b hcase420a hcase420b hcase300b hcase310b hcase331a hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase40
                              omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase341b hcase431a hcase030b hcase410b hcase420a hcase420b hcase300a hcase300b hcase400b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase44
                            omega
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase431a hcase030a hcase030b hcase410a hcase410b hcase420a hcase420b hcase300b hcase311a hcase401a hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase431a hcase030b hcase410a hcase410b hcase420a hcase420b hcase300b hcase311a hcase401a hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase33
                              omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase321b hcase131a hcase131b hcase010a hcase010b hcase431a hcase431b hcase030a hcase030b hcase410a hcase410b hcase420a hcase420b hcase301a hcase301b hcase400a hcase400b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase321b hcase131a hcase131b hcase010a hcase010b hcase341a hcase341b hcase431a hcase030a hcase030b hcase410b hcase420b hcase400b hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33
                            omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase431a hcase030a hcase030b hcase410a hcase410b hcase420a hcase420b hcase301a hcase301b hcase401a hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase321b hcase131a hcase131b hcase010a hcase010b hcase341a hcase341b hcase431a hcase030a hcase030b hcase410b hcase420a hcase420b hcase301a hcase301b hcase401a hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33
                            omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase341b hcase431a hcase030b hcase410b hcase421a hcase400b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase321b hcase131a hcase131b hcase010a hcase010b hcase341a hcase341b hcase431a hcase030a hcase030b hcase410b hcase421a hcase401a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase44
                        omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase341b hcase431a hcase030a hcase030b hcase411a hcase310a hcase310b hcase400b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase42
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase341b hcase431a hcase030a hcase030b hcase411a hcase310a hcase310b hcase400b hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase42
                          omega
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase431a hcase431b hcase030a hcase030b hcase310b hcase420a hcase420b hcase300b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase44
                            omega
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase431a hcase030a hcase030b hcase411a hcase310b hcase401a hcase420b hcase301a hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase010a hcase010b hcase341a hcase341b hcase431a hcase030a hcase030b hcase411a hcase310a hcase310b hcase401a hcase420a hcase420b hcase301a hcase301b hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase33
                              omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase010a hcase010b hcase341a hcase341b hcase431a hcase030a hcase030b hcase411a hcase310a hcase310b hcase401a hcase421a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase44
                          omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase341b hcase431a hcase030a hcase030b hcase411a hcase311a hcase311b hcase400b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase42
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase341b hcase431a hcase030a hcase030b hcase411a hcase311a hcase311b hcase400b hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase42
                          omega
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                          ·
                            clear hn4 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase431a hcase030b hcase411a hcase311a hcase401a hcase420a hcase420b hcase300b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase431a hcase030a hcase030b hcase411a hcase311a hcase401a hcase420b hcase301a hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase010a hcase010b hcase341a hcase341b hcase431a hcase030a hcase030b hcase411a hcase311a hcase311b hcase401a hcase421a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase44
                          omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase341b hcase431a hcase400b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase41 hcase42
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase010a hcase010b hcase341a hcase341b hcase431a hcase031a hcase400b hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase41 hcase42
                      omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase321b hcase131a hcase131b hcase010a hcase010b hcase431a hcase431b hcase031a hcase031b hcase401a hcase401b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase41 hcase42
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase010a hcase010b hcase341a hcase341b hcase431a hcase031a hcase401a hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase41 hcase42
                      omega
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase300b hcase310b hcase330b hcase340b hcase00 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase030b hcase300b hcase310b hcase330b hcase341a hcase00 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase300a hcase300b hcase310b hcase331a hcase420a hcase420b hcase430a hcase430b hcase340b hcase00 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase030b hcase300b hcase310b hcase331a hcase420b hcase430b hcase341a hcase00 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase44
                          omega
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase300a hcase300b hcase310b hcase331a hcase420a hcase420b hcase431a hcase431b hcase340b hcase00 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase030b hcase300b hcase310b hcase331a hcase420a hcase420b hcase431a hcase341a hcase00 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase44
                          omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase300a hcase300b hcase310b hcase331a hcase421a hcase421b hcase340b hcase00 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase030b hcase300b hcase310b hcase331a hcase421a hcase341a hcase00 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase43 hcase44
                        omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase321a hcase131a hcase131b hcase011a hcase030b hcase300a hcase300b hcase400b hcase410b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase34 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase300b hcase311a hcase400a hcase400b hcase411a hcase411b hcase340b hcase330b hcase00 hcase04 hcase10 hcase11 hcase12 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase300a hcase300b hcase311a hcase400a hcase400b hcase411a hcase411b hcase340b hcase331a hcase00 hcase04 hcase10 hcase11 hcase12 hcase42 hcase43 hcase44
                          omega
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase321a hcase131a hcase131b hcase011a hcase030b hcase300b hcase311a hcase400a hcase400b hcase411a hcase411b hcase341a hcase330b hcase00 hcase04 hcase10 hcase11 hcase12 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase321a hcase131a hcase131b hcase011a hcase030b hcase300b hcase311a hcase400a hcase400b hcase411a hcase341a hcase331a hcase00 hcase04 hcase10 hcase11 hcase12 hcase42 hcase43 hcase44
                          omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase300b hcase311a hcase401a hcase401b hcase340b hcase330b hcase00 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase300a hcase300b hcase311a hcase401a hcase401b hcase340b hcase331a hcase00 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase321a hcase131a hcase131b hcase011a hcase030b hcase300b hcase311a hcase401a hcase401b hcase341a hcase330b hcase00 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase321a hcase131a hcase131b hcase011a hcase030b hcase300b hcase311a hcase401a hcase341a hcase331a hcase00 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                        omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase301a hcase410a hcase410b hcase420a hcase420b hcase430a hcase430b hcase340b hcase310b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase40 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase301a hcase410a hcase410b hcase420a hcase420b hcase430a hcase430b hcase340b hcase311a hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase40 hcase44
                          omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase321b hcase131a hcase131b hcase030a hcase030b hcase301a hcase301b hcase410a hcase410b hcase420a hcase420b hcase430a hcase430b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase40
                          omega
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat1 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase030b hcase301a hcase410b hcase420b hcase430b hcase341a hcase441a hcase310b hcase400b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase030a hcase030b hcase301a hcase410a hcase410b hcase420b hcase430b hcase341a hcase441a hcase310b hcase401a hcase00 hcase04 hcase10 hcase11 hcase12 hcase33
                              omega
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut2 hcut49 hcut53 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase321a hcase131a hcase131b hcase011a hcase030b hcase301a hcase410b hcase420b hcase430b hcase341a hcase441a hcase311a hcase400b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33
                              omega
                            ·
                              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                              ·
                                clear hn4 hsum_nat1 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase030a hcase030b hcase301a hcase410a hcase410b hcase420b hcase430a hcase430b hcase341a hcase441a hcase311a hcase401a hcase330b hcase00 hcase04 hcase10 hcase11 hcase12
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase301a hcase410a hcase410b hcase420b hcase430a hcase430b hcase341a hcase441a hcase311a hcase401a hcase331a hcase00 hcase04 hcase10 hcase11 hcase12
                                omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase301a hcase410a hcase410b hcase420a hcase420b hcase431a hcase431b hcase340b hcase310b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase40 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase301a hcase410a hcase410b hcase420a hcase420b hcase431a hcase431b hcase340b hcase311a hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase40 hcase44
                          omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase030b hcase301a hcase301b hcase410b hcase420a hcase420b hcase431a hcase341a hcase341b hcase400b hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase44
                          omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase321b hcase131a hcase131b hcase030a hcase030b hcase301a hcase301b hcase410a hcase410b hcase420a hcase420b hcase431a hcase431b hcase401a hcase401b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase030a hcase030b hcase301a hcase301b hcase410a hcase410b hcase420a hcase420b hcase431a hcase341a hcase341b hcase401a hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33
                            omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase030b hcase301a hcase301b hcase410b hcase421a hcase400b hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase43 hcase44
                      omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase321b hcase131a hcase131b hcase030a hcase030b hcase301a hcase301b hcase410a hcase410b hcase421a hcase421b hcase401a hcase401b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase030a hcase030b hcase301a hcase301b hcase410a hcase410b hcase421a hcase401a hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase43
                        omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase301a hcase411a hcase411b hcase400a hcase400b hcase420a hcase420b hcase430a hcase430b hcase340b hcase310b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase301a hcase411a hcase411b hcase400a hcase400b hcase420a hcase420b hcase430a hcase430b hcase340b hcase311a hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase44
                            omega
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            clear hn4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase030a hcase030b hcase301a hcase411a hcase400b hcase420b hcase430b hcase341a hcase310b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase44
                            omega
                          ·
                            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                            ·
                              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                              ·
                                clear hn4 hsum_nat0 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut10 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase301a hcase411a hcase400b hcase420b hcase430b hcase341a hcase311a hcase330b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12
                                omega
                              ·
                                clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase030a hcase030b hcase301a hcase301b hcase411a hcase400b hcase420a hcase420b hcase430a hcase430b hcase341a hcase341b hcase311a hcase311b hcase330a hcase330b hcase441a hcase00 hcase04 hcase10 hcase11 hcase12
                                omega
                            ·
                              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hcut9 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase301a hcase411a hcase400a hcase400b hcase420b hcase430b hcase341a hcase311a hcase440b hcase00 hcase04 hcase10 hcase11 hcase12
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase301a hcase411a hcase400a hcase400b hcase420b hcase430a hcase430b hcase341a hcase311a hcase331a hcase441a hcase00 hcase04 hcase10 hcase11 hcase12
                                omega
                      ·
                        clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase030a hcase030b hcase301a hcase301b hcase411a hcase400b hcase420a hcase420b hcase431a hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase030a hcase030b hcase301a hcase301b hcase411a hcase400b hcase421a hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase43 hcase44
                      omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase301a hcase411a hcase411b hcase401a hcase401b hcase420a hcase420b hcase340b hcase310b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase301a hcase411a hcase411b hcase401a hcase401b hcase420a hcase420b hcase340b hcase311a hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase43 hcase44
                          omega
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase321b hcase131a hcase131b hcase030a hcase030b hcase301a hcase301b hcase411a hcase411b hcase401a hcase401b hcase420a hcase420b hcase330a hcase330b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase030a hcase030b hcase301a hcase411a hcase401a hcase420b hcase341a hcase330b hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase43
                            omega
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              clear hn4 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase030a hcase030b hcase301a hcase411a hcase401a hcase420b hcase341a hcase331a hcase310b hcase430b hcase00 hcase04 hcase10 hcase11 hcase12 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase030a hcase030b hcase301a hcase301b hcase411a hcase401a hcase420a hcase420b hcase341a hcase341b hcase331a hcase331b hcase310a hcase310b hcase431a hcase00 hcase04 hcase10 hcase11 hcase12 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase030a hcase030b hcase301a hcase411a hcase401a hcase420b hcase341a hcase331a hcase311a hcase00 hcase04 hcase10 hcase11 hcase12 hcase43 hcase44
                            omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase030a hcase030b hcase301a hcase301b hcase411a hcase401a hcase421a hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase33 hcase34 hcase43 hcase44
                      omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase321b hcase131a hcase131b hcase011a hcase011b hcase031a hcase031b hcase400b hcase410b hcase420b hcase430b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase34
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase031a hcase400b hcase410a hcase410b hcase420a hcase420b hcase430a hcase430b hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase34
                        omega
                    ·
                      clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase031a hcase400b hcase410a hcase410b hcase420a hcase420b hcase431a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase34 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase031a hcase400b hcase410a hcase410b hcase421a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase34 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase031a hcase400b hcase411a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase031a hcase031b hcase401a hcase401b hcase300b hcase340b hcase310b hcase330b hcase00 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase031a hcase031b hcase300b hcase340a hcase340b hcase310b hcase331a hcase00 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase401a hcase401b hcase300b hcase340b hcase311a hcase330b hcase00 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase031a hcase031b hcase401a hcase401b hcase300a hcase300b hcase340b hcase311a hcase331a hcase00 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase031a hcase300b hcase341a hcase330b hcase310b hcase00 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase401a hcase401b hcase300b hcase341a hcase330b hcase311a hcase420a hcase420b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase41 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase031a hcase401a hcase300a hcase300b hcase341a hcase330b hcase311a hcase420b hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase41 hcase43
                            omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase031a hcase401a hcase300a hcase300b hcase341a hcase341b hcase330a hcase330b hcase311a hcase311b hcase421a hcase00 hcase04 hcase10 hcase11 hcase12 hcase41 hcase43 hcase44
                          omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase031a hcase031b hcase401a hcase300a hcase300b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase41 hcase42 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase031a hcase401a hcase300a hcase300b hcase341a hcase341b hcase331a hcase331b hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase31 hcase41 hcase42 hcase43
                        omega
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase031a hcase031b hcase401a hcase401b hcase301a hcase310b hcase420a hcase420b hcase430a hcase430b hcase340b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase41 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase031a hcase401a hcase301a hcase310b hcase420b hcase430b hcase341a hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase41 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase031a hcase401a hcase301a hcase301b hcase310a hcase310b hcase420a hcase420b hcase431a hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase34 hcase41 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase031a hcase401a hcase301a hcase301b hcase310a hcase310b hcase421a hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase34 hcase41 hcase43 hcase44
                      omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase031a hcase031b hcase401a hcase401b hcase301a hcase311a hcase420a hcase420b hcase430a hcase430b hcase340b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase41 hcase44
                          omega
                        ·
                          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat1 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase031a hcase401a hcase301a hcase311a hcase420b hcase430b hcase330b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase41
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase031a hcase401a hcase301a hcase301b hcase311a hcase311b hcase420a hcase420b hcase430a hcase430b hcase341a hcase341b hcase330a hcase330b hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase41
                              omega
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut9 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase031a hcase031b hcase401a hcase301a hcase311a hcase420b hcase430b hcase341a hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase41
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase131b hcase011a hcase011b hcase031a hcase031b hcase401a hcase301a hcase311a hcase420b hcase430a hcase430b hcase341a hcase331a hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase41
                              omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase031a hcase401a hcase301a hcase301b hcase311a hcase311b hcase420a hcase420b hcase431a hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase34 hcase41 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase020a hcase020b hcase141a hcase141b hcase321a hcase131a hcase011a hcase031a hcase401a hcase301a hcase301b hcase311a hcase311b hcase421a hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase34 hcase41 hcase43 hcase44
                      omega
  ·
    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
    ·
      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
      ·
        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase010a hcase010b hcase430a hcase430b hcase320b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
          omega
        ·
          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase010a hcase010b hcase430a hcase430b hcase321a hcase030a hcase030b hcase130b hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
              omega
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase021a hcase021b hcase010a hcase010b hcase430a hcase430b hcase321a hcase030a hcase030b hcase131a hcase131b hcase340b hcase300b hcase310b hcase330b hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase40 hcase41 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase021a hcase021b hcase010a hcase010b hcase430a hcase430b hcase321a hcase030a hcase030b hcase131a hcase131b hcase340b hcase300a hcase300b hcase310b hcase331a hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase40 hcase41 hcase42 hcase44
                      omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase021a hcase021b hcase010a hcase010b hcase430a hcase430b hcase321a hcase321b hcase030a hcase030b hcase131a hcase131b hcase340a hcase340b hcase300a hcase300b hcase311a hcase311b hcase140b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase40 hcase41 hcase42 hcase44
                      omega
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase021a hcase021b hcase010a hcase010b hcase430a hcase430b hcase321a hcase030a hcase030b hcase131a hcase131b hcase340b hcase300b hcase311a hcase141a hcase330b hcase00 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase021a hcase021b hcase010a hcase010b hcase430a hcase430b hcase321a hcase030a hcase030b hcase131a hcase131b hcase340b hcase300a hcase300b hcase311a hcase141a hcase141b hcase331a hcase00 hcase04 hcase10 hcase11 hcase12 hcase40 hcase41 hcase42 hcase44
                        omega
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase021a hcase021b hcase010a hcase010b hcase430a hcase430b hcase321a hcase030a hcase030b hcase131a hcase131b hcase340b hcase301a hcase310b hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase33 hcase40 hcase41 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase021a hcase021b hcase010a hcase010b hcase430a hcase430b hcase321a hcase030a hcase030b hcase131a hcase131b hcase340b hcase301a hcase311a hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase33 hcase40 hcase41 hcase42 hcase44
                    omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase010b hcase430b hcase321a hcase030b hcase131a hcase131b hcase341a hcase341b hcase400b hcase410b hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase33 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase010b hcase430b hcase321a hcase030a hcase030b hcase131a hcase131b hcase341a hcase341b hcase400b hcase411a hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase33 hcase42 hcase44
                    omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase021a hcase021b hcase010a hcase010b hcase430a hcase430b hcase321a hcase321b hcase030a hcase030b hcase131a hcase131b hcase401a hcase401b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase33 hcase41 hcase42
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase010b hcase430b hcase321a hcase030a hcase030b hcase131a hcase341a hcase341b hcase401a hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase33 hcase41 hcase42
                    omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase010a hcase010b hcase430a hcase430b hcase321a hcase130b hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
              omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase010b hcase430b hcase321a hcase031a hcase131a hcase131b hcase400b hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase33 hcase34 hcase41 hcase42 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase010b hcase430b hcase321a hcase031a hcase131a hcase401a hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase33 hcase34 hcase41 hcase42 hcase44
                omega
      ·
        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase010a hcase010b hcase400a hcase400b hcase320b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase41 hcase42 hcase44
            omega
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase010a hcase010b hcase431a hcase400b hcase321a hcase030b hcase410b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                omega
              ·
                clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase010a hcase010b hcase431a hcase400b hcase321a hcase030a hcase030b hcase411a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                omega
            ·
              clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase010a hcase010b hcase431a hcase400b hcase321a hcase031a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase41 hcase42 hcase44
              omega
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase010a hcase010b hcase401a hcase401b hcase130b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase44
            omega
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase021a hcase021b hcase010a hcase010b hcase431a hcase431b hcase401a hcase401b hcase131a hcase131b hcase140b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase44
              omega
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase010a hcase010b hcase401a hcase401b hcase131a hcase131b hcase141a hcase141b hcase310a hcase310b hcase320b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase41 hcase42 hcase44
                  omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase021a hcase021b hcase010a hcase010b hcase431a hcase431b hcase401a hcase401b hcase131a hcase131b hcase141a hcase141b hcase310b hcase321a hcase330b hcase340b hcase300b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase021a hcase021b hcase010a hcase010b hcase431a hcase431b hcase401a hcase401b hcase131a hcase131b hcase141a hcase141b hcase310b hcase321a hcase330a hcase330b hcase340b hcase301a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase44
                        omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase021a hcase021b hcase010a hcase010b hcase431a hcase431b hcase401a hcase401b hcase131a hcase131b hcase141a hcase141b hcase310a hcase310b hcase321a hcase321b hcase330a hcase330b hcase440b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase41 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase010a hcase010b hcase431a hcase401a hcase131a hcase141a hcase141b hcase310a hcase310b hcase321a hcase330a hcase330b hcase341a hcase341b hcase441a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase41 hcase42
                        omega
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase021a hcase021b hcase010a hcase010b hcase431a hcase431b hcase131a hcase131b hcase141a hcase141b hcase310b hcase321a hcase331a hcase300b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase34 hcase41 hcase42 hcase44
                      omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase021a hcase021b hcase010a hcase010b hcase431a hcase431b hcase401a hcase401b hcase131a hcase131b hcase141a hcase141b hcase310b hcase321a hcase331a hcase301a hcase340b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase44
                        omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase010a hcase010b hcase431a hcase401a hcase131a hcase131b hcase141a hcase141b hcase310b hcase321a hcase301a hcase341a hcase440b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase010a hcase010b hcase431a hcase401a hcase131a hcase141a hcase141b hcase310a hcase310b hcase321a hcase331a hcase331b hcase301a hcase301b hcase341a hcase341b hcase441a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42
                          omega
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase010a hcase010b hcase401a hcase401b hcase131a hcase131b hcase141a hcase141b hcase311a hcase311b hcase030a hcase030b hcase320b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase41 hcase42 hcase44
                    omega
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase021a hcase021b hcase010a hcase010b hcase431a hcase431b hcase401a hcase401b hcase131a hcase131b hcase141a hcase311a hcase030a hcase030b hcase321a hcase300b hcase330b hcase340b hcase00 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase010a hcase010b hcase431a hcase401a hcase131a hcase131b hcase141a hcase311a hcase030b hcase321a hcase300b hcase330a hcase330b hcase341a hcase00 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat1 hcut9 hcut64 hcut40 hcut25 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase010a hcase010b hcase431a hcase401a hcase131a hcase131b hcase141a hcase311a hcase030b hcase321a hcase300b hcase331a hcase00 hcase04 hcase10 hcase11 hcase12 hcase34 hcase41 hcase42 hcase44
                        omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut9 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase010a hcase010b hcase431a hcase401a hcase131a hcase131b hcase141a hcase141b hcase311a hcase030a hcase030b hcase321a hcase301a hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase34 hcase41 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase010a hcase010b hcase431a hcase401a hcase131a hcase141a hcase141b hcase311a hcase311b hcase030a hcase030b hcase321a hcase301a hcase301b hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase33 hcase34 hcase41 hcase42
                        omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase010a hcase010b hcase401a hcase401b hcase131a hcase131b hcase141a hcase141b hcase311a hcase311b hcase031a hcase031b hcase320b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase41 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase010a hcase010b hcase431a hcase401a hcase131a hcase141a hcase141b hcase311a hcase311b hcase031a hcase321a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase41 hcase42 hcase44
                    omega
    ·
      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase130b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
      ·
        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase021a hcase021b hcase011a hcase011b hcase131a hcase131b hcase140b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase131a hcase131b hcase141a hcase141b hcase310a hcase310b hcase320b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase011a hcase131a hcase131b hcase141a hcase141b hcase310a hcase310b hcase321a hcase400b hcase410b hcase030b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase011a hcase131a hcase131b hcase141a hcase141b hcase310a hcase310b hcase321a hcase400b hcase410a hcase410b hcase031a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase011a hcase131a hcase131b hcase141a hcase141b hcase310a hcase310b hcase321a hcase400b hcase411a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase021a hcase021b hcase011a hcase011b hcase131a hcase131b hcase141a hcase141b hcase310b hcase321a hcase401a hcase401b hcase340b hcase300b hcase330b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase021a hcase021b hcase011a hcase011b hcase131a hcase131b hcase141a hcase141b hcase310b hcase321a hcase340a hcase340b hcase300b hcase331a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut67 hcut66 hcut52 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase021a hcase021b hcase011a hcase011b hcase131a hcase131b hcase141a hcase141b hcase310b hcase321a hcase401a hcase401b hcase340b hcase301a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase33 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase131a hcase131b hcase141a hcase141b hcase310a hcase310b hcase321a hcase401a hcase440b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase41 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase011a hcase131a hcase141a hcase141b hcase310a hcase310b hcase321a hcase401a hcase341a hcase341b hcase441a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase41 hcase42 hcase43
                    omega
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase131a hcase131b hcase141a hcase141b hcase311a hcase311b hcase410a hcase410b hcase440b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase32 hcase33 hcase34 hcase40 hcase42 hcase43
                omega
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut4 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase011a hcase131a hcase131b hcase141a hcase410b hcase441a hcase030b hcase400b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase32 hcase33 hcase34 hcase42 hcase43
                    omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase131a hcase131b hcase141a hcase141b hcase311a hcase311b hcase410a hcase410b hcase441a hcase441b hcase030a hcase030b hcase401a hcase401b hcase320b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase011a hcase131a hcase141a hcase141b hcase311a hcase311b hcase410a hcase410b hcase441a hcase030a hcase030b hcase401a hcase321a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase42 hcase43
                      omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase131a hcase131b hcase141a hcase141b hcase311a hcase311b hcase410a hcase410b hcase441a hcase441b hcase031a hcase031b hcase320b hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase40 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase011a hcase131a hcase141a hcase141b hcase311a hcase311b hcase410a hcase410b hcase441a hcase031a hcase321a hcase00 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase40 hcase42 hcase43
                    omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut4 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase041a hcase041b hcase131a hcase131b hcase141a hcase141b hcase311a hcase311b hcase411a hcase411b hcase320b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase40 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut28 hcut12 hcut36 hcut2 hcut49 hcut53 hcut61 hcut16 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase011a hcase131a hcase131b hcase141a hcase141b hcase311a hcase311b hcase411a hcase321a hcase400b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut9 hcut64 hcut40 hcut25 hcut1 hcut17 hcut14 hcut28 hcut12 hcut36 hcut49 hcut53 hcut61 hcut16 hcut10 hcut48 hcut32 hcut18 hcut55 hcut66 hcut52 hcut59 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase041a hcase021a hcase011a hcase131a hcase141a hcase141b hcase311a hcase311b hcase411a hcase321a hcase401a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase30 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega

#print axioms symbolic_mask567_integer_shard002
end Jsp404.SixExactFloorKernel
