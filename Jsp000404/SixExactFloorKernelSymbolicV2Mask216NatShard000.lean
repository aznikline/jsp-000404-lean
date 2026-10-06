import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask216_integer_shard000 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut50 : (s00 + s44 + u00 + u44) + 1 ≤ (n))
    (hcut79 : (s00 + s04 + s11 + s40 + s44 + u00 + u04 + u11 + u40 + u44) + 1 ≤ (2 * n))
    (hcut54 : (s00 + s02 + s04 + u00 + u02 + u04) + 1 ≤ (n + 1))
    (hcut13 : (s02 + s03 + s30 + u02 + u03 + u30) + 1 ≤ (n))
    (hcut27 : (s00 + s04 + s40 + u00 + u04 + u40 + 2) + 1 ≤ (2 * n))
    (hcut2 : (s00 + s11 + s33 + s44 + u00 + u11 + u33 + u44) + 1 ≤ (n + 2))
    (hcut64 : (s04 + s10 + s11 + s33 + s40 + s44 + u04 + u10 + u11 + u33 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut9 : (s11 + s44 + u11 + u44) + 1 ≤ (n))
    (hcut96 : (s00 + s34 + s43 + u00 + u34 + u43) + 1 ≤ (n + 1))
    (hcut73 : (s33 + s44 + u33 + u44) + 1 ≤ (n))
    (hcut12 : (s03 + s41 + u03 + u41 + 1) + 1 ≤ (n))
    (hcut86 : (s13 + s31 + s42 + u13 + u31 + u42 + 1) + 1 ≤ (n))
    (hcut93 : (s00 + s03 + s04 + s11 + s40 + s44 + u00 + u03 + u04 + u11 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut70 : (s44 + u44 + 1) + 1 ≤ (n))
    (hcut87 : (s13 + s14 + s41 + s42 + u13 + u14 + u41 + u42) + 1 ≤ (n))
    (hcut53 : (s10 + s33 + s44 + u10 + u33 + u44) + 1 ≤ (n + 1))
    (hcut4 : (s02 + s30 + s31 + s34 + s42 + s43 + u02 + u30 + u31 + u34 + u42 + u43) + 1 ≤ (n + 1))
    (hcut3 : (s00 + s03 + s04 + s41 + u00 + u03 + u04 + u41) + 1 ≤ (n + s31 + 3))
    (hcut15 : (s10 + s11 + s34 + u10 + u11 + u34) + 1 ≤ (n + 1))
    (hcut94 : (s01 + s02 + s03 + s04 + u01 + u02 + u03 + u04) + 1 ≤ (n))
    (hcut44 : (s01 + s32 + u01 + u32) + 1 ≤ (s11 + 2))
    (hcut52 : (s00 + s04 + s11 + s30 + s41 + s44 + u00 + u04 + u11 + u30 + u41 + u44) + 1 ≤ (2 * n + 2))
    (hcut0 : (s12 + s43 + u12 + u43) + 1 ≤ (s33 + 2))
    (hcut92 : (s01 + s02 + s04 + u01 + u02 + u04) + 1 ≤ (n))
    (hcut101 : (s02 + s03 + s04 + s31 + u02 + u03 + u04 + u31) + 1 ≤ (n))
    (hcut100 : (s11 + s43 + s44 + u11 + u43 + u44) + 1 ≤ (n + 1))
    (hcut14 : (s00 + s02 + s13 + u00 + u02 + u13) + 1 ≤ (n + 1))
    (hcut98 : (s12 + s32 + s44 + u12 + u32 + u44) + 1 ≤ (n + 1))
    (hcut99 : (s04 + s11 + s12 + s34 + u04 + u11 + u12 + u34) + 1 ≤ (2 * n))
    (hcut102 : (s00 + s04 + s11 + s33 + s40 + u00 + u04 + u11 + u33 + u40) + 1 ≤ (2 * n))
    (hcut61 : (s03 + s14 + s30 + s31 + u03 + u14 + u30 + u31) + 1 ≤ (n + 1))
    (hcut8 : (s03 + s40 + u03 + u40) + 1 ≤ (n))
    (hcut58 : (s04 + s41 + u04 + u41) + 1 ≤ (n))
    (hcut91 : (s40 + s41 + s42 + u40 + u41 + u42) + 1 ≤ (n))
    (hcut63 : (s12 + s30 + s31 + s32 + s44 + u12 + u30 + u31 + u32 + u44) + 1 ≤ (n + 2))
    (hcut104 : (s00 + s04 + s11 + s33 + s34 + s40 + u00 + u04 + u11 + u33 + u34 + u40) + 1 ≤ (2 * n + 1))
    (hcut103 : (s00 + s04 + s12 + s32 + s34 + s40 + u00 + u04 + u12 + u32 + u34 + u40) + 1 ≤ (2 * n + 1))
    (hcut29 : (s00 + s33 + s40 + u00 + u33 + u40 + 1) + 1 ≤ (2 * n))
    (hcut5 : (s03 + s04 + s40 + s41 + u03 + u04 + u40 + u41) + 1 ≤ (n + 2))
    (hcut76 : (s40 + s41 + s43 + u40 + u41 + u43) + 1 ≤ (n))
    (hcut1 : (s00 + u00) + 1 ≤ (s10 + 3))
    (hcut77 : (s02 + s04 + u02 + u04) + 1 ≤ (n))
    (hcut37 : (s00 + s04 + s11 + s12 + s40 + u00 + u04 + u11 + u12 + u40) + 1 ≤ (2 * n))
    (hcut57 : (s04 + s30 + u04 + u30) + 1 ≤ (n))
    (hcut49 : (s00 + s02 + s43 + u00 + u02 + u43) + 1 ≤ (n + 1))
    (hcut62 : (s30 + s31 + s44 + u30 + u31 + u44) + 1 ≤ (n + 1))
    (hcut95 : (s13 + s14 + s30 + s31 + u13 + u14 + u30 + u31) + 1 ≤ (n + 1))
    (hcut68 : (s10 + u10) + 1 ≤ (s00 + 2))
    (hcut78 : (s02 + s03 + s04 + u02 + u03 + u04) + 1 ≤ (n))
    (hcut59 : (s04 + s12 + s40 + s44 + u04 + u12 + u40 + u44 + 1) + 1 ≤ (2 * n))
    (hcut28 : (s00 + s04 + s11 + s40 + u00 + u04 + u11 + u40 + 1) + 1 ≤ (2 * n))
    (hcut11 : (s02 + u02 + 1) + 1 ≤ (n))
    (hcut31 : (s14 + s40 + u14 + u40) + 1 ≤ (n))
    (hcut80 : (s00 + s04 + s33 + s40 + s44 + u00 + u04 + u33 + u40 + u44) + 1 ≤ (2 * n))
    (hcut107 : (s34 + u34) + 1 ≤ (s44 + 2))
    (hcut110 : (s40 + s41 + s42 + s43 + u40 + u41 + u42 + u43) + 1 ≤ (n))
    (hcut111 : (s13 + s30 + s31 + s42 + u13 + u30 + u31 + u42) + 1 ≤ (n))
    (hcut112 : (s02 + s13 + s30 + s42 + u02 + u13 + u30 + u42) + 1 ≤ (n))
    (hcut113 : (s13 + s14 + s30 + s42 + u13 + u14 + u30 + u42) + 1 ≤ (n + 1))
    (hcut114 : (s00 + s12 + s13 + s14 + u00 + u12 + u13 + u14) + 1 ≤ (n + 1))
    (hcut115 : (s00 + s11 + s13 + s14 + s40 + s41 + s42 + s44 + u00 + u11 + u13 + u14 + u40 + u41 + u42 + u44) + 1 ≤ (2 * n + 2))
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
    (hcase010a : s01 = 0)
    (hcase010b : u01 = 0)
    (hcase020a : s02 = 0)
    (hcase020b : u02 = 0)
    (hcase030a : s03 = 0)
    (hcase030b : u03 = 0)
    (hcase040a : s04 = 0)
    (hcase040b : u04 = 0)
    : False := by
  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
  ·
    clear hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030b hcase040b hcase000b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
    omega
  ·
    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
    ·
      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
      ·
        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
        ·
          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              clear hsum_nat0 hsum_nat1 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320b hcase310b hcase300b hcase340b hcase330b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hsum_nat1 hsum_nat3 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030b hcase040b hcase001a hcase320a hcase320b hcase310a hcase310b hcase300a hcase300b hcase340a hcase340b hcase331a hcase331b hcase420b hcase410b hcase400b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030b hcase040b hcase001a hcase320b hcase310b hcase300b hcase340b hcase331a hcase420a hcase420b hcase410a hcase410b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase43 hcase44
                    omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030a hcase030b hcase040b hcase001a hcase320a hcase320b hcase310a hcase310b hcase300a hcase300b hcase340a hcase340b hcase331a hcase331b hcase420b hcase411a hcase400b hcase430b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase310a hcase310b hcase300a hcase300b hcase340a hcase340b hcase331a hcase331b hcase420a hcase420b hcase411a hcase400a hcase400b hcase431a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase310a hcase310b hcase300a hcase300b hcase340a hcase340b hcase331a hcase331b hcase420a hcase420b hcase411a hcase401a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase43 hcase44
                    omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hsum_nat1 hcut50 hcut79 hcut54 hcut13 hcut27 hcut64 hcut9 hcut96 hcut73 hcut12 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030b hcase040b hcase001a hcase320b hcase310a hcase310b hcase300b hcase340b hcase331a hcase421a hcase410b hcase430b hcase400b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase310a hcase310b hcase300a hcase300b hcase340a hcase340b hcase331a hcase331b hcase421a hcase410a hcase410b hcase430a hcase430b hcase401a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase310a hcase310b hcase300a hcase300b hcase340a hcase340b hcase331a hcase331b hcase421a hcase410a hcase410b hcase431a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase310a hcase310b hcase300a hcase300b hcase340a hcase340b hcase331a hcase331b hcase421a hcase411a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase43 hcase44
                  omega
          ·
            clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030b hcase040b hcase001a hcase320a hcase320b hcase310a hcase310b hcase300a hcase300b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
        ·
          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                clear hsum_nat1 hsum_nat3 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030b hcase040b hcase001a hcase320a hcase320b hcase310a hcase310b hcase301a hcase301b hcase410b hcase400b hcase420b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase34 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020a hcase020b hcase030b hcase040b hcase001a hcase320a hcase320b hcase310a hcase310b hcase410b hcase400b hcase421a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase34 hcase43 hcase44
                omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut54 hcut13 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030b hcase040b hcase001a hcase320a hcase320b hcase310a hcase310b hcase301a hcase301b hcase410b hcase401a hcase420b hcase430b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase34 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase310a hcase310b hcase301a hcase301b hcase410a hcase410b hcase401a hcase420a hcase420b hcase431a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase34 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase310a hcase310b hcase301a hcase301b hcase410a hcase410b hcase401a hcase421a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase34 hcase43 hcase44
                omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030a hcase030b hcase040b hcase001a hcase320a hcase320b hcase310a hcase310b hcase301a hcase301b hcase411a hcase400b hcase420b hcase430b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase34 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase310a hcase310b hcase301a hcase301b hcase411a hcase400a hcase400b hcase420a hcase420b hcase431a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase34 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase310a hcase310b hcase301a hcase301b hcase411a hcase400a hcase400b hcase421a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase34 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase310a hcase310b hcase301a hcase301b hcase411a hcase401a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase34 hcase42 hcase43 hcase44
              omega
      ·
        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030b hcase040b hcase001a hcase320a hcase320b hcase340a hcase340b hcase400b hcase430b hcase410b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase42 hcase44
                omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030a hcase030b hcase040b hcase001a hcase320a hcase320b hcase311a hcase311b hcase340a hcase340b hcase400b hcase430b hcase411a hcase420b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase311a hcase311b hcase340a hcase340b hcase400a hcase400b hcase430a hcase430b hcase411a hcase421a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase44
                  omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030b hcase040b hcase001a hcase320a hcase320b hcase311a hcase311b hcase340a hcase340b hcase400a hcase400b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase41 hcase42 hcase44
              omega
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hn4 hsum_nat1 hcut79 hcut54 hcut13 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030b hcase040b hcase001a hcase320b hcase311a hcase340b hcase401a hcase330b hcase300b hcase410b hcase430b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase311a hcase311b hcase340a hcase340b hcase401a hcase330a hcase330b hcase300a hcase300b hcase410a hcase410b hcase431a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase42 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase311a hcase311b hcase340a hcase340b hcase401a hcase330a hcase330b hcase300a hcase300b hcase411a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hn4 hsum_nat1 hcut79 hcut54 hcut13 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030b hcase040b hcase001a hcase320b hcase311a hcase340b hcase401a hcase330b hcase301a hcase410b hcase430b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase311a hcase311b hcase340a hcase340b hcase401a hcase330a hcase330b hcase301a hcase301b hcase410a hcase410b hcase431a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase42 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase311a hcase311b hcase340a hcase340b hcase401a hcase330a hcase330b hcase301a hcase301b hcase411a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030b hcase040b hcase001a hcase320a hcase320b hcase311a hcase311b hcase340a hcase340b hcase401a hcase410b hcase420b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase311a hcase311b hcase340a hcase340b hcase401a hcase331a hcase331b hcase410a hcase410b hcase421a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase040a hcase040b hcase001a hcase001b hcase320a hcase320b hcase311a hcase311b hcase340a hcase340b hcase401a hcase331a hcase331b hcase411a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase42 hcase43 hcase44
                omega
        ·
          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut44 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut1 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase030b hcase040b hcase001a hcase320a hcase320b hcase311a hcase311b hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
    ·
      clear hn4 hsum_nat3 hsum_nat4 hcut50 hcut79 hcut54 hcut13 hcut27 hcut2 hcut64 hcut9 hcut96 hcut73 hcut12 hcut86 hcut93 hcut70 hcut87 hcut53 hcut4 hcut3 hcut15 hcut94 hcut52 hcut0 hcut92 hcut101 hcut100 hcut14 hcut98 hcut99 hcut102 hcut61 hcut8 hcut58 hcut91 hcut63 hcut104 hcut103 hcut29 hcut5 hcut76 hcut77 hcut37 hcut57 hcut49 hcut62 hcut95 hcut68 hcut78 hcut59 hcut28 hcut11 hcut31 hcut80 hcut107 hcut110 hcut111 hcut112 hcut113 hcut114 hcut115 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase020b hcase030b hcase040b hcase001a hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega

#print axioms symbolic_v2_mask216_integer_shard000
end Jsp404.SixExactFloorKernel
