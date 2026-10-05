import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_mask79_integer_shard000 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut79 : (s04 + s12 + s30 + s31 + u04 + u12 + u30 + u31) + 1 ≤ (n))
    (hcut46 : (s10 + s12 + u10 + u12 + 1) + 1 ≤ (n))
    (hcut34 : (s34 + u34) + 1 ≤ (s44 + 2))
    (hcut33 : (s11 + s12 + u11 + u12 + 2) + 1 ≤ (n))
    (hcut58 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 1))
    (hcut57 : (s00 + s33 + s44 + u00 + u33 + u44) + 1 ≤ (n + 2))
    (hcut44 : (s02 + s10 + u02 + u10) + 1 ≤ (n))
    (hcut74 : (s00 + s04 + s13 + s40 + s44 + u00 + u04 + u13 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut32 : (s03 + s10 + s11 + s12 + u03 + u10 + u11 + u12) + 1 ≤ (n))
    (hcut1 : (s00 + s04 + s13 + s33 + s40 + s44 + u00 + u04 + u13 + u33 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut12 : (s01 + s02 + s13 + s14 + s32 + s40 + s42 + s44 + u01 + u02 + u13 + u14 + u32 + u40 + u42 + u44) + 1 ≤ (2 * n + 1))
    (hcut81 : (s12 + s14 + u12 + u14 + 2) + 1 ≤ (n))
    (hcut78 : (s01 + s02 + s42 + s43 + u01 + u02 + u42 + u43) + 1 ≤ (s33 + 2))
    (hcut56 : (s03 + s10 + s14 + s32 + s33 + s40 + u03 + u10 + u14 + u32 + u33 + u40) + 1 ≤ (2 * n + 1))
    (hcut35 : (s12 + s30 + u12 + u30 + 2) + 1 ≤ (n))
    (hcut54 : (s03 + s11 + s12 + s14 + u03 + u11 + u12 + u14) + 1 ≤ (n))
    (hcut21 : (s10 + s11 + s40 + u10 + u11 + u40 + 2) + 1 ≤ (2 * n))
    (hcut77 : (s03 + s41 + u03 + u41) + 1 ≤ (s13 + 2))
    (hcut66 : (s40 + s42 + u40 + u42) + 1 ≤ (n))
    (hcut31 : (s10 + s32 + s40 + u10 + u32 + u40 + 2) + 1 ≤ (2 * n))
    (hcut5 : (s02 + s10 + s11 + s42 + s43 + s44 + u02 + u10 + u11 + u42 + u43 + u44) + 1 ≤ (n + 2))
    (hcut41 : (s14 + s40 + u14 + u40) + 1 ≤ (n + 1))
    (hcut14 : (s40 + s41 + s42 + s44 + u40 + u41 + u42 + u44) + 1 ≤ (n + 1))
    (hcut26 : (s01 + s43 + u01 + u43) + 1 ≤ (s33 + 1))
    (hcut36 : (s31 + s40 + u31 + u40 + 3) + 1 ≤ (2 * n))
    (hcut43 : (s13 + s40 + u13 + u40) + 1 ≤ (n))
    (hcut0 : (s11 + s12 + s30 + s31 + s34 + s41 + s42 + s43 + u11 + u12 + u30 + u31 + u34 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut2 : (s44 + u44) + 1 ≤ (s34 + 3))
    (hcut68 : (s00 + s33 + u00 + u33) + 1 ≤ (n + 1))
    (hcut13 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut37 : (s30 + s31 + s40 + u30 + u31 + u40 + 2) + 1 ≤ (2 * n))
    (hcut59 : (s00 + s04 + s40 + s44 + u00 + u04 + u40 + u44) + 1 ≤ (2 * n))
    (hcut15 : (s02 + s11 + s14 + s31 + u02 + u11 + u14 + u31) + 1 ≤ (n))
    (hcut80 : (s10 + s14 + s32 + s33 + s40 + s44 + u10 + u14 + u32 + u33 + u40 + u44) + 1 ≤ (2 * n + 1))
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
    : False := by
  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
  ·
    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
    ·
      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
      ·
        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
        ·
          clear hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase000b hcase010b hcase040b hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          clear hn4 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase000b hcase010b hcase041a hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
        ·
          clear hn4 hsum_nat1 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase000b hcase011a hcase040b hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            clear hn4 hsum_nat1 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase000b hcase011a hcase041a hcase140b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  clear hn4 hsum_nat1 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030b hcase000b hcase011a hcase041a hcase141a hcase130a hcase130b hcase400b hcase410b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase000a hcase000b hcase011a hcase011b hcase041a hcase041b hcase141a hcase141b hcase130b hcase400a hcase400b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat1 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase000b hcase011a hcase041a hcase141a hcase130a hcase130b hcase401a hcase410b hcase420b hcase440b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut14 hcut36 hcut43 hcut0 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase000b hcase011a hcase041a hcase141a hcase130a hcase130b hcase401a hcase410b hcase420b hcase441a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase43
                      omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat1 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030b hcase000b hcase011a hcase041a hcase141a hcase130a hcase130b hcase401a hcase410b hcase421a hcase440b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut14 hcut26 hcut36 hcut43 hcut0 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030b hcase000b hcase011a hcase041a hcase141a hcase130a hcase130b hcase401a hcase410b hcase421a hcase441a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase43
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase000a hcase000b hcase011a hcase011b hcase041a hcase041b hcase141a hcase141b hcase130b hcase401a hcase401b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat1 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030b hcase000b hcase011a hcase041a hcase141a hcase131a hcase131b hcase410b hcase400b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase000b hcase011a hcase041a hcase141a hcase410b hcase401a hcase420a hcase420b hcase330b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase000a hcase000b hcase011a hcase041a hcase141a hcase141b hcase410b hcase401a hcase420b hcase331a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                      omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030b hcase000b hcase011a hcase041a hcase141a hcase410b hcase401a hcase330b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030b hcase000a hcase000b hcase011a hcase041a hcase141a hcase141b hcase410b hcase401a hcase421a hcase331a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                      omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030a hcase030b hcase000b hcase011a hcase041a hcase141a hcase141b hcase131a hcase131b hcase411a hcase430a hcase430b hcase400b hcase420b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                      omega
                    ·
                      clear hn4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase000b hcase011a hcase041a hcase141a hcase141b hcase131a hcase131b hcase411a hcase430a hcase430b hcase400b hcase421a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                      omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase000a hcase000b hcase011a hcase011b hcase041a hcase041b hcase141a hcase141b hcase131a hcase411a hcase430b hcase401a hcase420b hcase440b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase000b hcase011a hcase041a hcase141a hcase131a hcase411a hcase430b hcase401a hcase420a hcase420b hcase441a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34
                        omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase000b hcase011a hcase041a hcase141a hcase131a hcase411a hcase430b hcase401a hcase421a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                      omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase000b hcase011a hcase041a hcase141a hcase141b hcase131b hcase411a hcase411b hcase330b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase40 hcase42 hcase44
                    omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030a hcase030b hcase000a hcase000b hcase011a hcase041a hcase141a hcase141b hcase131a hcase131b hcase411a hcase431a hcase331a hcase420b hcase400b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030a hcase030b hcase000a hcase000b hcase011a hcase041a hcase141a hcase141b hcase131a hcase411a hcase431a hcase331a hcase420b hcase401a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                        omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        clear hn4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase000b hcase011a hcase041a hcase141a hcase141b hcase131a hcase131b hcase411a hcase431a hcase331a hcase331b hcase421a hcase400b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase000a hcase000b hcase011a hcase041a hcase141a hcase141b hcase131a hcase411a hcase431a hcase331a hcase421a hcase401a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                        omega
    ·
      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
      ·
        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
        ·
          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                clear hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase400b hcase330b hcase410b hcase040b hcase420b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                omega
              ·
                clear hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030b hcase001a hcase400b hcase330b hcase410b hcase040b hcase421a hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase400a hcase400b hcase330a hcase330b hcase410a hcase410b hcase140b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase400b hcase330b hcase410b hcase041a hcase141a hcase420b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase400a hcase400b hcase330b hcase410a hcase410b hcase041a hcase041b hcase141a hcase141b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
          ·
            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
            ·
              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase400b hcase330b hcase411a hcase420b hcase440b hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43
                omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030a hcase030b hcase001a hcase400b hcase330b hcase411a hcase420b hcase441a hcase040b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43
                  omega
                ·
                  clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030a hcase030b hcase001a hcase400b hcase330b hcase411a hcase420b hcase441a hcase041a hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase400a hcase400b hcase330b hcase411a hcase411b hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
              omega
        ·
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase400a hcase400b hcase040b hcase010b hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase400a hcase400b hcase331a hcase040b hcase011a hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase400a hcase400b hcase331a hcase331b hcase140b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase400b hcase331a hcase041a hcase141a hcase410b hcase420b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030b hcase001a hcase400b hcase331a hcase041a hcase141a hcase410b hcase421a hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030a hcase030b hcase001a hcase400b hcase331a hcase041a hcase141a hcase141b hcase411a hcase440b hcase420b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase400b hcase331a hcase041a hcase141a hcase141b hcase411a hcase440b hcase421a hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43
                    omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030a hcase030b hcase001a hcase400b hcase331a hcase041a hcase141a hcase141b hcase411a hcase441a hcase420b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase400b hcase331a hcase041a hcase141a hcase141b hcase411a hcase441a hcase421a hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43
                    omega
      ·
        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
        ·
          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                          ·
                            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                            ·
                              rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                              ·
                                clear hsum_nat0 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330b hcase410b hcase420b hcase340a hcase340b hcase310a hcase310b hcase440b hcase100b hcase110b hcase120b hcase02 hcase13 hcase30 hcase32 hcase43
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330b hcase410b hcase420b hcase340a hcase340b hcase310a hcase310b hcase440b hcase100b hcase110b hcase121a hcase02 hcase13 hcase30 hcase32 hcase43
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hcut79 hcut46 hcut34 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330b hcase410b hcase420b hcase340a hcase340b hcase310a hcase310b hcase440b hcase100b hcase111a hcase02 hcase12 hcase13 hcase30 hcase32 hcase43
                              omega
                          ·
                            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase140a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330b hcase410b hcase420b hcase340b hcase310b hcase440b hcase300b hcase02 hcase11 hcase12 hcase13 hcase32 hcase43
                              omega
                            ·
                              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                              ·
                                clear hn4 hsum_nat0 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut54 hcut21 hcut77 hcut66 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330b hcase410b hcase420b hcase340b hcase310b hcase440b hcase101a hcase301a hcase110b hcase02 hcase12 hcase13 hcase32 hcase43
                                omega
                              ·
                                rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                                ·
                                  clear hn4 hsum_nat0 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330b hcase410b hcase420b hcase340a hcase340b hcase310a hcase310b hcase440b hcase101a hcase301a hcase301b hcase111a hcase120b hcase02 hcase13 hcase32 hcase43
                                  omega
                                ·
                                  clear hn4 hsum_nat0 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330b hcase410b hcase420b hcase340a hcase340b hcase310a hcase310b hcase440b hcase101a hcase301a hcase301b hcase111a hcase121a hcase02 hcase13 hcase32 hcase43
                                  omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase401b hcase140a hcase140b hcase010b hcase040b hcase330a hcase330b hcase410a hcase410b hcase420a hcase420b hcase340a hcase340b hcase310a hcase310b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase32 hcase43
                          omega
                      ·
                        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                        ·
                          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                          ·
                            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                            ·
                              rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                              ·
                                clear hsum_nat0 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase140b hcase010a hcase010b hcase040a hcase040b hcase330a hcase330b hcase410a hcase410b hcase420a hcase420b hcase340a hcase340b hcase311a hcase311b hcase130b hcase100b hcase110b hcase120b hcase02 hcase30 hcase32 hcase43 hcase44
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase140b hcase010a hcase010b hcase040a hcase040b hcase330a hcase330b hcase410a hcase410b hcase420a hcase420b hcase340a hcase340b hcase311a hcase311b hcase130b hcase100b hcase110a hcase110b hcase121a hcase02 hcase30 hcase32 hcase43 hcase44
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase140b hcase010a hcase010b hcase040a hcase040b hcase330a hcase330b hcase410a hcase410b hcase420a hcase420b hcase340a hcase340b hcase311a hcase311b hcase130b hcase100b hcase111a hcase02 hcase12 hcase30 hcase32 hcase43 hcase44
                              omega
                          ·
                            rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                            ·
                              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                              ·
                                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                                ·
                                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                                  ·
                                    clear hn4 hsum_nat0 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut5 hcut41 hcut14 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330b hcase410b hcase420b hcase340b hcase311a hcase130b hcase101a hcase120b hcase440b hcase110b hcase300b hcase02 hcase32 hcase43
                                    omega
                                  ·
                                    clear hn4 hsum_nat0 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330b hcase410b hcase420b hcase340b hcase311a hcase130b hcase101a hcase120b hcase440b hcase110b hcase301a hcase02 hcase32 hcase43
                                    omega
                                ·
                                  clear hn4 hsum_nat0 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330b hcase410b hcase420b hcase340a hcase340b hcase311a hcase311b hcase130b hcase101a hcase120b hcase440b hcase111a hcase02 hcase30 hcase32 hcase43
                                  omega
                              ·
                                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase401b hcase140a hcase140b hcase010b hcase040b hcase330a hcase330b hcase410a hcase410b hcase420a hcase420b hcase340a hcase340b hcase311a hcase311b hcase130a hcase130b hcase101a hcase101b hcase120a hcase120b hcase02 hcase11 hcase30 hcase32 hcase43
                                omega
                            ·
                              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut79 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase140b hcase010a hcase010b hcase040a hcase040b hcase330a hcase330b hcase410a hcase410b hcase420a hcase420b hcase340a hcase340b hcase311a hcase311b hcase130b hcase101a hcase121a hcase110b hcase02 hcase30 hcase32 hcase43 hcase44
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase140b hcase010a hcase010b hcase040a hcase040b hcase330a hcase330b hcase410a hcase410b hcase420a hcase420b hcase340a hcase340b hcase311a hcase311b hcase130b hcase101a hcase121a hcase111a hcase02 hcase30 hcase32 hcase43 hcase44
                                omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase140a hcase140b hcase010a hcase010b hcase040b hcase330b hcase410b hcase420b hcase340a hcase340b hcase311a hcase311b hcase02 hcase10 hcase11 hcase12 hcase30 hcase32 hcase43 hcase44
                          omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase140a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330a hcase330b hcase410a hcase410b hcase420a hcase420b hcase440b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase401b hcase140a hcase140b hcase010b hcase040b hcase330a hcase330b hcase410a hcase410b hcase420a hcase420b hcase341a hcase341b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase43
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase140a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330b hcase410a hcase410b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                    omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase140a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330a hcase330b hcase440a hcase440b hcase420a hcase420b hcase130b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase140a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330b hcase411a hcase440b hcase420b hcase131a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase140a hcase140b hcase010a hcase010b hcase040a hcase040b hcase330b hcase411a hcase411b hcase440a hcase440b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43
                      omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase401b hcase140a hcase140b hcase010b hcase040b hcase330a hcase330b hcase411a hcase411b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43
                    omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase401b hcase140a hcase140b hcase010b hcase040b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase140b hcase010a hcase010b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase140a hcase140b hcase040a hcase040b hcase330b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase401b hcase140a hcase140b hcase011a hcase040b hcase331a hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase140b hcase011a hcase011b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase420b hcase040a hcase040b hcase010a hcase010b hcase330b hcase440b hcase130a hcase130b hcase410b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase141a hcase141b hcase420a hcase420b hcase040a hcase040b hcase010a hcase010b hcase330a hcase330b hcase440a hcase440b hcase130b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43
                        omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase141a hcase141b hcase420b hcase040a hcase040b hcase010a hcase010b hcase330b hcase440b hcase410b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase141a hcase141b hcase420b hcase040a hcase040b hcase010a hcase010b hcase330b hcase440b hcase131a hcase411a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43
                        omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase401b hcase141a hcase141b hcase420a hcase420b hcase040b hcase010b hcase330a hcase330b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                    omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase401b hcase141a hcase141b hcase420a hcase420b hcase040b hcase010b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43 hcase44
                  omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase141a hcase141b hcase420a hcase420b hcase040a hcase040b hcase330b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase401b hcase141a hcase141b hcase420a hcase420b hcase040b hcase011a hcase331a hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43 hcase44
                  omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase420b hcase041a hcase041b hcase410b hcase010a hcase010b hcase330b hcase440b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase141a hcase141b hcase420b hcase041a hcase410b hcase010a hcase010b hcase330b hcase441a hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43
                      omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase420b hcase041a hcase041b hcase410b hcase010a hcase010b hcase331a hcase331b hcase430b hcase440b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase141a hcase141b hcase420b hcase041a hcase410b hcase010b hcase430b hcase441a hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34
                        omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut14 hcut36 hcut43 hcut0 hcut2 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase141a hcase420b hcase041a hcase410b hcase010a hcase010b hcase331a hcase431a hcase440b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase141a hcase141b hcase420b hcase041a hcase410b hcase010a hcase010b hcase331a hcase431a hcase441a hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34
                        omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase141a hcase420b hcase410b hcase440b hcase330b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut14 hcut36 hcut43 hcut0 hcut2 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase141a hcase420b hcase041a hcase410b hcase011a hcase440b hcase331a hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43
                      omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase141a hcase141b hcase420a hcase420b hcase041a hcase041b hcase410a hcase410b hcase441a hcase441b hcase330b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase141a hcase420b hcase041a hcase410b hcase011a hcase441a hcase331a hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43
                      omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase141a hcase141b hcase420a hcase420b hcase041a hcase041b hcase130b hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase43 hcase44
                  omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase141a hcase141b hcase420b hcase041a hcase041b hcase411a hcase131a hcase330b hcase440b hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030a hcase030b hcase001a hcase401a hcase141a hcase141b hcase420b hcase041a hcase411a hcase131a hcase330b hcase441a hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43
                      omega
                  ·
                    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030a hcase030b hcase001a hcase401a hcase141a hcase141b hcase420b hcase041a hcase411a hcase131a hcase010b hcase430b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030a hcase030b hcase001a hcase401a hcase141a hcase141b hcase420b hcase041a hcase411a hcase131a hcase331a hcase010a hcase010b hcase431a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030a hcase030b hcase001a hcase401a hcase141a hcase141b hcase420b hcase041a hcase411a hcase131a hcase331a hcase011a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                      omega
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase141a hcase141b hcase330b hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43 hcase44
              omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030b hcase001a hcase401a hcase141a hcase141b hcase331a hcase410b hcase040b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase141a hcase141b hcase421a hcase331a hcase331b hcase410b hcase041a hcase041b hcase440b hcase430b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030b hcase001a hcase401a hcase141a hcase421a hcase331a hcase410b hcase041a hcase440b hcase431a hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34
                      omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase141a hcase141b hcase421a hcase331a hcase331b hcase410a hcase410b hcase041a hcase041b hcase441a hcase430b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030b hcase001a hcase401a hcase141a hcase141b hcase421a hcase331a hcase410b hcase041a hcase441a hcase431a hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34
                      omega
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase030b hcase001a hcase401a hcase401b hcase141a hcase141b hcase421a hcase421b hcase411a hcase411b hcase010b hcase040b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                    omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase141a hcase141b hcase421a hcase331a hcase331b hcase411a hcase010a hcase010b hcase041a hcase041b hcase430b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase44
                      omega
                    ·
                      rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase141a hcase141b hcase421a hcase421b hcase331a hcase331b hcase010a hcase010b hcase041a hcase041b hcase431a hcase431b hcase130b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase401a hcase141a hcase141b hcase421a hcase331a hcase411a hcase010a hcase010b hcase041a hcase431a hcase131a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase44
                        omega
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut26 hcut36 hcut43 hcut0 hcut2 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030b hcase001a hcase401a hcase141a hcase141b hcase331a hcase411a hcase011a hcase040b hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                    omega
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase401a hcase401b hcase141a hcase141b hcase421a hcase421b hcase331a hcase331b hcase011a hcase011b hcase041a hcase041b hcase130b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase030a hcase030b hcase001a hcase401a hcase141a hcase141b hcase421a hcase331a hcase411a hcase011a hcase041a hcase131a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                      omega
  ·
    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
    ·
      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
      ·
        rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
        ·
          clear hn4 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase040b hcase000b hcase010b hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase000a hcase000b hcase011a hcase011b hcase130b hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                clear hn4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase040b hcase000b hcase011a hcase131a hcase131b hcase400b hcase420b hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43 hcase44
                omega
              ·
                clear hn4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase040b hcase000b hcase011a hcase131a hcase131b hcase400b hcase421a hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43 hcase44
                omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                clear hn4 hsum_nat1 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase040b hcase000b hcase011a hcase131a hcase401a hcase420b hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut0 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase040b hcase000b hcase011a hcase131a hcase401a hcase421a hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43 hcase44
                omega
      ·
        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
        ·
          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
          ·
            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase330a hcase330b hcase420a hcase420b hcase440a hcase440b hcase130b hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase43
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase330b hcase420b hcase440b hcase131a hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase43
                omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase040b hcase001a hcase330b hcase420b hcase441a hcase400b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase330a hcase330b hcase420a hcase420b hcase441a hcase441b hcase401a hcase401b hcase130b hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase040b hcase001a hcase330b hcase420b hcase441a hcase401a hcase131a hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                  omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase001a hcase001b hcase330b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase43 hcase44
            omega
        ·
          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
          ·
            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase010a hcase010b hcase420b hcase400b hcase410b hcase430b hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase331a hcase010a hcase010b hcase420b hcase400b hcase410b hcase431a hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                    omega
                ·
                  clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase040b hcase001a hcase331a hcase010a hcase010b hcase420b hcase400b hcase411a hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase331a hcase331b hcase010a hcase010b hcase420a hcase420b hcase401a hcase401b hcase130b hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43 hcase44
                  omega
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase040b hcase001a hcase010b hcase420b hcase401a hcase131a hcase430b hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase040b hcase001a hcase331a hcase010a hcase010b hcase420b hcase401a hcase131a hcase431a hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase44
                    omega
            ·
              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase040b hcase001a hcase331a hcase010a hcase010b hcase421a hcase440b hcase400b hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                  omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase040b hcase001a hcase331a hcase010a hcase010b hcase440b hcase401a hcase130b hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut0 hcut2 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase040b hcase001a hcase331a hcase010a hcase010b hcase421a hcase440b hcase401a hcase131a hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                    omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase331a hcase331b hcase010a hcase010b hcase421a hcase421b hcase441a hcase441b hcase130b hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase43
                  omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase040b hcase001a hcase331a hcase010a hcase010b hcase421a hcase441a hcase131a hcase131b hcase400b hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase040b hcase001a hcase331a hcase010a hcase010b hcase421a hcase441a hcase131a hcase401a hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                    omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase040a hcase040b hcase001a hcase001b hcase331a hcase331b hcase011a hcase011b hcase130b hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase331a hcase131a hcase131b hcase400b hcase410b hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase040b hcase001a hcase331a hcase011a hcase131a hcase131b hcase400b hcase411a hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase040b hcase001a hcase331a hcase011a hcase131a hcase401a hcase420b hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase040b hcase001a hcase331a hcase011a hcase131a hcase401a hcase421a hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43 hcase44
                  omega
    ·
      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
      ·
        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase000a hcase000b hcase140b hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase000a hcase000b hcase141a hcase141b hcase130b hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
              ·
                clear hn4 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase000b hcase141a hcase141b hcase131a hcase131b hcase400a hcase400b hcase010b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase000b hcase141a hcase141b hcase131a hcase131b hcase400b hcase011a hcase420b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43 hcase44
                  omega
                ·
                  clear hn4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase041a hcase000b hcase141a hcase141b hcase131a hcase131b hcase400b hcase011a hcase421a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43 hcase44
                  omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                  ·
                    clear hn4 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase000b hcase141a hcase141b hcase131a hcase131b hcase401a hcase401b hcase420a hcase420b hcase440a hcase440b hcase010b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43
                    omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut14 hcut36 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase000b hcase141a hcase131a hcase401a hcase420b hcase440b hcase011a hcase330b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                      omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase000b hcase141a hcase131a hcase131b hcase401a hcase420b hcase440b hcase011a hcase331a hcase410b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase000a hcase000b hcase141a hcase141b hcase131a hcase401a hcase420b hcase440a hcase440b hcase011a hcase331a hcase411a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase43
                        omega
                ·
                  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                  ·
                    clear hn4 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase000b hcase141a hcase141b hcase131a hcase131b hcase401a hcase401b hcase420a hcase420b hcase441a hcase441b hcase010b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase43
                    omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase000a hcase000b hcase141a hcase141b hcase131a hcase131b hcase401a hcase401b hcase420a hcase420b hcase441a hcase441b hcase330b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase000a hcase000b hcase141a hcase141b hcase131a hcase401a hcase420b hcase441a hcase011a hcase331a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                      omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase041a hcase000b hcase141a hcase141b hcase131a hcase131b hcase401a hcase401b hcase330b hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43 hcase44
                  omega
                ·
                  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                  ·
                    clear hn4 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase000b hcase141a hcase141b hcase131a hcase131b hcase401a hcase401b hcase421a hcase421b hcase331a hcase331b hcase010b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43 hcase44
                    omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase041a hcase000b hcase141a hcase131a hcase401a hcase421a hcase331a hcase331b hcase011a hcase430b hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase041a hcase000a hcase000b hcase141a hcase141b hcase131a hcase401a hcase421a hcase331a hcase011a hcase431a hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase44
                      omega
      ·
        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase001a hcase001b hcase130b hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
          ·
            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase001a hcase001b hcase131a hcase131b hcase330b hcase440b hcase400b hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase041a hcase041b hcase001a hcase001b hcase131a hcase330b hcase440b hcase401a hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase43
                omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase001a hcase131a hcase131b hcase330b hcase441a hcase420b hcase400b hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase001a hcase131a hcase330b hcase441a hcase420b hcase401a hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase43
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase001a hcase001b hcase131a hcase131b hcase330b hcase441a hcase441b hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase43
                omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase001a hcase001b hcase131a hcase131b hcase331a hcase331b hcase400b hcase410b hcase440b hcase420b hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase001a hcase001b hcase131a hcase131b hcase331a hcase331b hcase400b hcase410b hcase440b hcase421a hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43
                    omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase131a hcase131b hcase331a hcase400b hcase410b hcase441a hcase420b hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut77 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase131a hcase131b hcase331a hcase400b hcase410b hcase441a hcase421a hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43
                    omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase001a hcase131a hcase131b hcase331a hcase400b hcase411a hcase420b hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase041a hcase001a hcase131a hcase131b hcase331a hcase400b hcase411a hcase421a hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase43 hcase44
                  omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase001a hcase131a hcase401a hcase420b hcase430b hcase010b hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase001a hcase131a hcase331a hcase401a hcase420b hcase430a hcase430b hcase011a hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase44
                    omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020b hcase031a hcase041a hcase001a hcase131a hcase331a hcase401a hcase420b hcase431a hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase44
                  omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut1 hcut12 hcut81 hcut78 hcut56 hcut35 hcut54 hcut21 hcut77 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase031b hcase041a hcase041b hcase001a hcase001b hcase131a hcase131b hcase331a hcase331b hcase401a hcase421a hcase430b hcase440b hcase410b hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase041a hcase001a hcase131a hcase331a hcase401a hcase421a hcase430a hcase430b hcase440a hcase440b hcase411a hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34
                      omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase041a hcase001a hcase131a hcase331a hcase401a hcase421a hcase430a hcase430b hcase441a hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41
                    omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut46 hcut34 hcut33 hcut58 hcut57 hcut44 hcut74 hcut32 hcut12 hcut81 hcut56 hcut35 hcut54 hcut21 hcut66 hcut31 hcut5 hcut41 hcut14 hcut26 hcut36 hcut43 hcut0 hcut2 hcut68 hcut13 hcut37 hcut59 hcut15 hcut80 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase020a hcase020b hcase031a hcase041a hcase001a hcase131a hcase331a hcase401a hcase421a hcase431a hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase44
                  omega

#print axioms symbolic_mask79_integer_shard000
end Jsp404.SixExactFloorKernel
