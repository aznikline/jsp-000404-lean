import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_mask31_integer_shard005 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut78 : (s02 + s03 + s14 + s42 + u02 + u03 + u14 + u42 + 1) + 1 ≤ (n))
    (hcut8 : (s11 + s12 + u11 + u12 + 2) + 1 ≤ (n))
    (hcut12 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut77 : (s10 + s11 + s12 + s13 + s14 + u10 + u11 + u12 + u13 + u14) + 1 ≤ (n + 1))
    (hcut75 : (s11 + s12 + s13 + s14 + u11 + u12 + u13 + u14) + 1 ≤ (n))
    (hcut40 : (s41 + s42 + u41 + u42 + 1) + 1 ≤ (n))
    (hcut1 : (s40 + s41 + s42 + s43 + s44 + u40 + u41 + u42 + u43 + u44) + 1 ≤ (n + 1))
    (hcut37 : (s00 + s13 + s33 + s40 + u00 + u13 + u33 + u40) + 1 ≤ (2 * n + 1))
    (hcut52 : (s01 + s43 + u01 + u43) + 1 ≤ (s33 + 2))
    (hcut27 : (s14 + s40 + u14 + u40) + 1 ≤ (n))
    (hcut9 : (s12 + s30 + u12 + u30 + 1) + 1 ≤ (n))
    (hcut13 : (s34 + u34) + 1 ≤ (s44 + 2))
    (hcut20 : (s10 + s31 + s32 + s33 + s40 + u10 + u31 + u32 + u33 + u40 + 1) + 1 ≤ (2 * n))
    (hcut11 : (s02 + s40 + u02 + u40) + 1 ≤ (n))
    (hcut26 : (s10 + s11 + u10 + u11) + 1 ≤ (s30 + 3))
    (hcut6 : (s40 + s43 + u40 + u43) + 1 ≤ (n))
    (hcut18 : (s10 + u10 + 2) + 1 ≤ (n))
    (hcut57 : (s01 + s13 + s14 + s40 + s44 + u01 + u13 + u14 + u40 + u44) + 1 ≤ (2 * n))
    (hcut36 : (s10 + s11 + s40 + u10 + u11 + u40 + 2) + 1 ≤ (2 * n))
    (hcut70 : (s01 + s02 + s04 + s10 + u01 + u02 + u04 + u10) + 1 ≤ (n))
    (hcut53 : (s02 + s03 + s41 + u02 + u03 + u41) + 1 ≤ (s13 + 2))
    (hcut65 : (s13 + s40 + s44 + u13 + u40 + u44) + 1 ≤ (n + s34 + 2))
    (hcut28 : (s00 + s13 + s40 + u00 + u13 + u40) + 1 ≤ (2 * n))
    (hcut54 : (s00 + s33 + s44 + u00 + u33 + u44) + 1 ≤ (n + 2))
    (hcut4 : (s02 + s14 + s40 + u02 + u14 + u40) + 1 ≤ (n + 2))
    (hcut38 : (s40 + s42 + u40 + u42) + 1 ≤ (n))
    (hcut56 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 1))
    (hcut49 : (s04 + s13 + s40 + u04 + u13 + u40) + 1 ≤ (n + 2))
    (hcut39 : (s42 + u42 + 2) + 1 ≤ (n))
    (hcut47 : (s03 + s41 + u03 + u41) + 1 ≤ (s13 + 1))
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
    (hcase040a : s04 = 0)
    (hcase040b : u04 = 0)
    (hcase001a : 1 ≤ s00)
    (hcase001b : u00 = 1)
    (hcase341a : 1 ≤ s34)
    (hcase341b : u34 = 1)
    : False := by
  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
  ·
    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
    ·
      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
      ·
        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
        ·
          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase330a hcase330b hcase010a hcase010b hcase420a hcase420b hcase430a hcase430b hcase440b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41
            omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase341b hcase330a hcase330b hcase010b hcase420a hcase420b hcase430a hcase430b hcase130b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41
              omega
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase341b hcase330a hcase330b hcase010b hcase420a hcase420b hcase430a hcase430b hcase131a hcase131b hcase030b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41
                omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase341b hcase330a hcase330b hcase010b hcase420b hcase430b hcase441a hcase131a hcase131b hcase031a hcase400b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut28 hcut54 hcut4 hcut38 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase330a hcase330b hcase010b hcase420b hcase430b hcase441a hcase131a hcase031a hcase401a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41
                  omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase330b hcase010a hcase010b hcase420a hcase420b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase44
          omega
      ·
        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
        ·
          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut49 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase341b hcase330a hcase330b hcase010b hcase421a hcase400b hcase030b hcase410b hcase430b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut49 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase341b hcase330b hcase010a hcase010b hcase421a hcase400b hcase030b hcase410b hcase431a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                omega
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut1 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase341b hcase330a hcase330b hcase010b hcase421a hcase400b hcase030b hcase411a hcase430b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase330a hcase330b hcase010a hcase010b hcase421a hcase400a hcase400b hcase030a hcase030b hcase411a hcase431a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                omega
          ·
            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase330a hcase330b hcase010a hcase010b hcase421a hcase421b hcase400a hcase400b hcase031a hcase031b hcase440b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
              omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040b hcase001a hcase341a hcase341b hcase330b hcase010a hcase010b hcase421a hcase400b hcase031a hcase441a hcase410b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase330a hcase330b hcase010a hcase010b hcase421a hcase400a hcase400b hcase031a hcase031b hcase441a hcase411a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43
                omega
        ·
          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase330a hcase330b hcase010a hcase010b hcase421a hcase421b hcase401a hcase401b hcase440b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
            omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase330a hcase330b hcase010a hcase010b hcase421a hcase401a hcase441a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
            omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase330b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega
  ·
    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
    ·
      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
      ·
        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase410a hcase410b hcase010b hcase430a hcase430b hcase130b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase42 hcase44
            omega
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase410a hcase410b hcase010b hcase430a hcase430b hcase131a hcase131b hcase030b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase42 hcase44
              omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase341a hcase341b hcase410b hcase010a hcase010b hcase430b hcase131a hcase131b hcase031a hcase031b hcase420b hcase400b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                  omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase341b hcase410a hcase410b hcase010b hcase430b hcase131a hcase031a hcase420b hcase401a hcase440b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase410a hcase410b hcase010b hcase430b hcase131a hcase031a hcase420b hcase401a hcase441a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34
                    omega
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase331a hcase331b hcase410a hcase410b hcase010a hcase010b hcase430a hcase430b hcase131a hcase131b hcase031a hcase031b hcase421a hcase421b hcase440b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40
                  omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040b hcase001a hcase341a hcase341b hcase410b hcase010b hcase430b hcase131a hcase131b hcase031a hcase421a hcase441a hcase400b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase331a hcase331b hcase410a hcase410b hcase010a hcase010b hcase430a hcase430b hcase131a hcase131b hcase031a hcase031b hcase421a hcase441a hcase401a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34
                    omega
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase410a hcase410b hcase010b hcase431a hcase431b hcase400a hcase400b hcase030b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase44
              omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                clear hn4 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase341b hcase331a hcase410a hcase410b hcase010a hcase010b hcase431a hcase400b hcase031a hcase420b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040b hcase001a hcase341a hcase341b hcase331a hcase410b hcase010a hcase010b hcase431a hcase400b hcase031a hcase421a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                omega
          ·
            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase331a hcase331b hcase410a hcase410b hcase010a hcase010b hcase431a hcase431b hcase401a hcase401b hcase440b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase331a hcase331b hcase410a hcase410b hcase010a hcase010b hcase431a hcase401a hcase441a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42
              omega
      ·
        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase331a hcase331b hcase410a hcase410b hcase011a hcase011b hcase440b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase42 hcase43
          omega
        ·
          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase341b hcase331a hcase410a hcase410b hcase011a hcase420a hcase420b hcase130b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase43
              omega
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase341b hcase331a hcase410a hcase410b hcase011a hcase420a hcase420b hcase131a hcase131b hcase030b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase43
                omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase341a hcase341b hcase331a hcase410b hcase441a hcase420b hcase131a hcase131b hcase031a hcase031b hcase400b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase331a hcase410a hcase410b hcase011a hcase441a hcase420b hcase131a hcase031a hcase401a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43
                  omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040b hcase001a hcase341a hcase341b hcase331a hcase410b hcase011a hcase441a hcase421a hcase400b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase331a hcase331b hcase410a hcase410b hcase011a hcase011b hcase441a hcase421a hcase401a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43
              omega
    ·
      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
      ·
        rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
        ·
          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase411a hcase411b hcase030b hcase010b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
            ·
              clear hn4 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase341b hcase331a hcase411a hcase030a hcase030b hcase011a hcase400b hcase420b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut1 hcut37 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase341b hcase331a hcase411a hcase030b hcase011a hcase400b hcase421a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
              omega
          ·
            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase331a hcase331b hcase411a hcase411b hcase030a hcase030b hcase011a hcase011b hcase401a hcase401b hcase440b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase331a hcase331b hcase411a hcase030a hcase030b hcase011a hcase011b hcase401a hcase441a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43
              omega
      ·
        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
        ·
          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase331a hcase331b hcase420a hcase420b hcase430a hcase430b hcase010a hcase010b hcase130b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase44
                omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase341b hcase411a hcase031a hcase420b hcase430b hcase010b hcase131a hcase131b hcase400b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase411a hcase031a hcase420b hcase430b hcase010b hcase131a hcase401a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                  omega
            ·
              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase331a hcase331b hcase411a hcase411b hcase031a hcase031b hcase420a hcase420b hcase430a hcase430b hcase011a hcase011b hcase440b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40
                omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase331a hcase331b hcase420a hcase420b hcase430a hcase430b hcase011a hcase011b hcase441a hcase441b hcase130b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut27 hcut9 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase331a hcase411a hcase031a hcase420b hcase430a hcase430b hcase011a hcase441a hcase131a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40
                  omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              clear hn4 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut1 hcut37 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut4 hcut38 hcut56 hcut49 hcut39 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase040b hcase001a hcase341a hcase341b hcase331a hcase411a hcase031a hcase420b hcase431a hcase400b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase331a hcase331b hcase411a hcase031a hcase031b hcase420a hcase420b hcase431a hcase401a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
              omega
        ·
          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut1 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase331a hcase331b hcase411a hcase031a hcase031b hcase421a hcase430b hcase400b hcase440b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase331a hcase331b hcase411a hcase031a hcase031b hcase421a hcase430a hcase430b hcase400a hcase400b hcase441a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase331a hcase331b hcase411a hcase031a hcase031b hcase421a hcase430a hcase430b hcase401a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut78 hcut8 hcut12 hcut77 hcut75 hcut40 hcut37 hcut52 hcut27 hcut9 hcut13 hcut20 hcut11 hcut26 hcut6 hcut18 hcut57 hcut36 hcut70 hcut53 hcut65 hcut28 hcut54 hcut4 hcut38 hcut56 hcut49 hcut39 hcut47 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase341a hcase341b hcase331a hcase331b hcase411a hcase031a hcase031b hcase421a hcase431a hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase44
            omega

#print axioms symbolic_mask31_integer_shard005
end Jsp404.SixExactFloorKernel
