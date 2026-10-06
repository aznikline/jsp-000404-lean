import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask959_integer_shard003 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut1 : (s00 + s04 + s13 + s31 + s40 + s44 + u00 + u04 + u13 + u31 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut59 : (s12 + s14 + s32 + u12 + u14 + u32 + 2) + 1 ≤ (n))
    (hcut2 : (s13 + s14 + s30 + s31 + u13 + u14 + u30 + u31) + 1 ≤ (n + 1))
    (hcut33 : (s13 + s30 + u13 + u30 + 1) + 1 ≤ (n))
    (hcut68 : (s00 + s01 + s02 + s04 + u00 + u01 + u02 + u04) + 1 ≤ (n + 1))
    (hcut57 : (s00 + s04 + s13 + s31 + s34 + u00 + u04 + u13 + u31 + u34) + 1 ≤ (2 * n + 1))
    (hcut22 : (s14 + s31 + u14 + u31 + 1) + 1 ≤ (n))
    (hcut17 : (s03 + s10 + s14 + u03 + u10 + u14 + 1) + 1 ≤ (n))
    (hcut37 : (s10 + u10 + 2) + 1 ≤ (n))
    (hcut55 : (s32 + s33 + s34 + u32 + u33 + u34 + 1) + 1 ≤ (n))
    (hcut43 : (s40 + s42 + s43 + s44 + u40 + u42 + u43 + u44) + 1 ≤ (n + 1))
    (hcut20 : (s11 + s33 + s34 + s40 + u11 + u33 + u34 + u40) + 1 ≤ (n))
    (hcut60 : (s31 + s33 + s40 + u31 + u33 + u40) + 1 ≤ (n))
    (hcut38 : (s01 + s34 + u01 + u34) + 1 ≤ (s44 + 2))
    (hcut61 : (s01 + s10 + s13 + s14 + s31 + s34 + u01 + u10 + u13 + u14 + u31 + u34) + 1 ≤ (2 * n + 1))
    (hcut64 : (s30 + s32 + s33 + s34 + s41 + u30 + u32 + u33 + u34 + u41) + 1 ≤ (n))
    (hcut42 : (s10 + s43 + s44 + u10 + u43 + u44) + 1 ≤ (n + 2))
    (hcut5 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 2))
    (hcut14 : (s03 + s12 + s14 + u03 + u12 + u14 + 2) + 1 ≤ (n))
    (hcut13 : (s10 + s13 + s14 + s31 + s40 + s43 + s44 + u10 + u13 + u14 + u31 + u40 + u43 + u44) + 1 ≤ (2 * n + 2))
    (hcut69 : (s03 + s10 + s31 + s40 + s44 + u03 + u10 + u31 + u40 + u44) + 1 ≤ (2 * n))
    (hcut19 : (s12 + s33 + s34 + s40 + u12 + u33 + u34 + u40) + 1 ≤ (n))
    (hcut7 : (s11 + s12 + s41 + s42 + u11 + u12 + u41 + u42) + 1 ≤ (s31 + 2))
    (hcut0 : (s02 + s03 + s32 + s33 + u02 + u03 + u32 + u33) + 1 ≤ (s13 + 2))
    (hcut11 : (s02 + s14 + s43 + u02 + u14 + u43) + 1 ≤ (n))
    (hcut6 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut46 : (s33 + s34 + s41 + u33 + u34 + u41 + 2) + 1 ≤ (n))
    (hcut28 : (s13 + s31 + u13 + u31 + 1) + 1 ≤ (n))
    (hcut15 : (s03 + s11 + s14 + u03 + u11 + u14 + 2) + 1 ≤ (n))
    (hcut67 : (s01 + s02 + s10 + u01 + u02 + u10) + 1 ≤ (n))
    (hcut66 : (s30 + s31 + s32 + u30 + u31 + u32 + 1) + 1 ≤ (n))
    (hcut25 : (s10 + s43 + u10 + u43) + 1 ≤ (n + 1))
    (hcut58 : (s04 + s11 + s32 + u04 + u11 + u32 + 1) + 1 ≤ (n))
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
    (hcase011a : 1 ≤ s01)
    (hcase011b : u01 = 1)
    : False := by
  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
  ·
    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
    ·
      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
      ·
        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase310b hcase110a hcase110b hcase120a hcase120b hcase300b hcase330b hcase320b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase310b hcase110a hcase110b hcase120a hcase120b hcase300b hcase330b hcase321a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase310b hcase110a hcase110b hcase120a hcase120b hcase300b hcase331a hcase320b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase310b hcase110a hcase110b hcase120a hcase120b hcase300b hcase331a hcase321a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase310a hcase310b hcase110b hcase120b hcase301a hcase301b hcase130b hcase100b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase310a hcase310b hcase110b hcase120a hcase120b hcase301a hcase301b hcase130b hcase100b hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase310a hcase310b hcase110b hcase120b hcase301a hcase301b hcase130b hcase101a hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase310a hcase310b hcase110b hcase120b hcase301a hcase301b hcase130b hcase101a hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase310b hcase110a hcase110b hcase120a hcase120b hcase301a hcase330b hcase320b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase310b hcase110a hcase110b hcase120a hcase120b hcase301a hcase131a hcase330a hcase330b hcase321a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase310b hcase110a hcase110b hcase120a hcase120b hcase301a hcase131a hcase331a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase310b hcase110a hcase110b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase13 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase310b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase12 hcase13 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
    ·
      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
      ·
        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
        ·
          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase110b hcase120b hcase420a hcase420b hcase410a hcase410b hcase330a hcase330b hcase140b hcase300a hcase300b hcase320a hcase320b hcase100b hcase00 hcase01 hcase02 hcase03 hcase04 hcase13 hcase40 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110b hcase120b hcase420a hcase420b hcase410a hcase410b hcase330b hcase140b hcase300b hcase320b hcase101a hcase00 hcase01 hcase02 hcase03 hcase04 hcase13 hcase40 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase410a hcase410b hcase330b hcase140a hcase140b hcase300a hcase300b hcase321a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase13 hcase40 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase410a hcase410b hcase330b hcase140a hcase140b hcase301a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase13 hcase32 hcase40 hcase43 hcase44
                    omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase110b hcase120b hcase420a hcase420b hcase410a hcase410b hcase330a hcase330b hcase141a hcase130b hcase100b hcase00 hcase01 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110b hcase120b hcase420a hcase420b hcase410a hcase410b hcase330a hcase330b hcase141a hcase130b hcase101a hcase00 hcase01 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase43 hcase44
                      omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase410a hcase410b hcase330b hcase320b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase30 hcase40 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase410a hcase410b hcase330a hcase330b hcase131a hcase321a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase30 hcase40 hcase43 hcase44
                      omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase410a hcase410b hcase130b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase14 hcase30 hcase32 hcase40 hcase43 hcase44
                  omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase410a hcase410b hcase331a hcase131a hcase300b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase14 hcase32 hcase40 hcase43 hcase44
                    omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                      ·
                        clear hn4 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut46 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340b hcase110b hcase120b hcase420a hcase420b hcase410a hcase410b hcase331a hcase131a hcase301a hcase430a hcase430b hcase000b hcase01 hcase02 hcase03 hcase04 hcase10 hcase14 hcase32 hcase40 hcase44
                        omega
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase110b hcase120b hcase420a hcase420b hcase410a hcase410b hcase331a hcase131a hcase301a hcase430a hcase430b hcase001a hcase001b hcase040a hcase040b hcase100b hcase01 hcase02 hcase03 hcase14 hcase32 hcase40 hcase44
                            omega
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340b hcase110b hcase120b hcase420b hcase410b hcase331a hcase131a hcase301a hcase430b hcase001a hcase040b hcase101a hcase400b hcase01 hcase02 hcase03 hcase14 hcase32 hcase44
                              omega
                            ·
                              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                              ·
                                clear hn4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340b hcase110b hcase120b hcase420b hcase410b hcase331a hcase131a hcase301a hcase430b hcase001a hcase040b hcase101a hcase401a hcase320b hcase01 hcase02 hcase03 hcase14 hcase44
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase410a hcase410b hcase331a hcase131a hcase131b hcase301a hcase430a hcase430b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase401a hcase401b hcase321a hcase01 hcase02 hcase03 hcase14 hcase44
                                omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase410a hcase410b hcase331a hcase331b hcase131a hcase131b hcase301a hcase301b hcase430a hcase430b hcase001a hcase001b hcase041a hcase01 hcase02 hcase03 hcase10 hcase14 hcase32 hcase40 hcase44
                          omega
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase110b hcase120b hcase420a hcase420b hcase410a hcase410b hcase331a hcase331b hcase131a hcase431a hcase431b hcase100b hcase00 hcase01 hcase02 hcase03 hcase04 hcase14 hcase32 hcase40 hcase44
                        omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase110b hcase120b hcase420b hcase410b hcase331a hcase331b hcase131a hcase431a hcase101a hcase400b hcase00 hcase01 hcase02 hcase03 hcase04 hcase14 hcase32 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase410a hcase410b hcase331a hcase331b hcase131a hcase131b hcase301a hcase301b hcase431a hcase101a hcase101b hcase401a hcase00 hcase01 hcase02 hcase03 hcase04 hcase14 hcase32 hcase44
                          omega
            ·
              rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase110b hcase120b hcase420a hcase420b hcase411a hcase411b hcase000a hcase000b hcase100b hcase130b hcase01 hcase02 hcase03 hcase04 hcase14 hcase30 hcase32 hcase33 hcase40 hcase43 hcase44
                    omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase110b hcase120b hcase420a hcase420b hcase411a hcase411b hcase000a hcase000b hcase100b hcase131a hcase140b hcase01 hcase02 hcase03 hcase04 hcase30 hcase32 hcase33 hcase40 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase110b hcase120b hcase420a hcase420b hcase411a hcase411b hcase000a hcase000b hcase100b hcase131a hcase141a hcase01 hcase02 hcase03 hcase04 hcase30 hcase32 hcase33 hcase40 hcase43 hcase44
                      omega
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase411a hcase411b hcase000b hcase040b hcase030b hcase01 hcase02 hcase13 hcase14 hcase30 hcase32 hcase33 hcase40 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase411a hcase411b hcase000a hcase000b hcase101a hcase101b hcase040a hcase040b hcase031a hcase01 hcase02 hcase13 hcase14 hcase30 hcase32 hcase33 hcase40 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase411a hcase411b hcase000a hcase000b hcase101a hcase101b hcase041a hcase01 hcase02 hcase03 hcase13 hcase14 hcase30 hcase32 hcase33 hcase40 hcase43 hcase44
                    omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase110b hcase120b hcase420a hcase420b hcase411a hcase411b hcase001a hcase001b hcase130b hcase100b hcase01 hcase02 hcase03 hcase04 hcase14 hcase30 hcase32 hcase33 hcase40 hcase43 hcase44
                    omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase340a hcase340b hcase311a hcase311b hcase110b hcase120b hcase420a hcase420b hcase411a hcase411b hcase001a hcase001b hcase130b hcase101a hcase140b hcase01 hcase02 hcase03 hcase04 hcase30 hcase32 hcase33 hcase40 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110b hcase120b hcase420a hcase420b hcase411a hcase411b hcase001a hcase001b hcase130b hcase101a hcase141a hcase01 hcase02 hcase03 hcase04 hcase30 hcase32 hcase33 hcase40 hcase43 hcase44
                      omega
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase411a hcase411b hcase001a hcase001b hcase030a hcase030b hcase140a hcase140b hcase300b hcase320b hcase330b hcase01 hcase02 hcase04 hcase10 hcase40 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase411a hcase411b hcase001a hcase001b hcase131a hcase030a hcase030b hcase140a hcase140b hcase300b hcase320a hcase320b hcase331a hcase01 hcase02 hcase04 hcase10 hcase40 hcase43 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase411a hcase411b hcase001a hcase001b hcase131a hcase030a hcase030b hcase140a hcase140b hcase300b hcase321a hcase01 hcase02 hcase04 hcase10 hcase33 hcase40 hcase43 hcase44
                          omega
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase411a hcase411b hcase001a hcase001b hcase131a hcase131b hcase030a hcase030b hcase140a hcase140b hcase301a hcase330b hcase01 hcase02 hcase04 hcase10 hcase32 hcase40 hcase43 hcase44
                          omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                              ·
                                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                                ·
                                  clear hn4 hsum_nat0 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase110b hcase120b hcase420a hcase420b hcase001a hcase001b hcase131a hcase030a hcase030b hcase140b hcase301a hcase331a hcase400a hcase400b hcase430a hcase430b hcase040a hcase040b hcase100b hcase01 hcase02 hcase32 hcase44
                                  omega
                                ·
                                  clear hn4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut42 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340a hcase340b hcase311a hcase110b hcase120b hcase420b hcase411a hcase001a hcase131a hcase030b hcase140b hcase301a hcase331a hcase400b hcase430b hcase040b hcase101a hcase01 hcase02 hcase32 hcase44
                                  omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase411a hcase411b hcase001a hcase001b hcase131a hcase131b hcase030a hcase030b hcase140a hcase140b hcase301a hcase301b hcase331a hcase331b hcase400a hcase400b hcase430a hcase430b hcase041a hcase01 hcase02 hcase10 hcase32 hcase44
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase411a hcase001a hcase001b hcase131a hcase131b hcase030a hcase030b hcase140a hcase140b hcase301a hcase301b hcase331a hcase331b hcase400a hcase400b hcase431a hcase01 hcase02 hcase04 hcase10 hcase32 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase411a hcase001a hcase001b hcase131a hcase131b hcase030a hcase030b hcase140a hcase140b hcase301a hcase301b hcase331a hcase331b hcase401a hcase01 hcase02 hcase04 hcase10 hcase32 hcase43 hcase44
                            omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase411a hcase411b hcase001a hcase001b hcase030a hcase030b hcase320b hcase330b hcase01 hcase02 hcase04 hcase10 hcase30 hcase40 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase411a hcase411b hcase001a hcase001b hcase131a hcase030a hcase030b hcase320a hcase320b hcase331a hcase01 hcase02 hcase04 hcase10 hcase30 hcase40 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase411a hcase411b hcase001a hcase001b hcase131a hcase030a hcase030b hcase321a hcase01 hcase02 hcase04 hcase10 hcase30 hcase33 hcase40 hcase43 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase120a hcase120b hcase420a hcase420b hcase411a hcase411b hcase001a hcase001b hcase131a hcase131b hcase031a hcase01 hcase02 hcase04 hcase10 hcase14 hcase30 hcase32 hcase33 hcase40 hcase43 hcase44
                    omega
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase110b hcase120b hcase421a hcase421b hcase300a hcase300b hcase140b hcase320a hcase320b hcase330a hcase330b hcase100b hcase00 hcase01 hcase02 hcase03 hcase04 hcase13 hcase40 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110b hcase120b hcase421a hcase421b hcase300b hcase140b hcase320b hcase330b hcase101a hcase00 hcase01 hcase02 hcase03 hcase04 hcase13 hcase40 hcase41 hcase43 hcase44
                      omega
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase120a hcase120b hcase421a hcase421b hcase300a hcase300b hcase140a hcase140b hcase320a hcase320b hcase130b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase40 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase421a hcase421b hcase300b hcase140a hcase140b hcase320a hcase320b hcase331a hcase131a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase40 hcase41 hcase43 hcase44
                      omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase421a hcase421b hcase300a hcase300b hcase140a hcase140b hcase130b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase33 hcase40 hcase41 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase421a hcase421b hcase300b hcase140a hcase140b hcase321a hcase131a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase33 hcase40 hcase41 hcase43 hcase44
                    omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase421a hcase421b hcase300b hcase130b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase32 hcase33 hcase40 hcase41 hcase43 hcase44
                  omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase421a hcase421b hcase300b hcase131a hcase131b hcase330b hcase320b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase40 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase421a hcase421b hcase300a hcase300b hcase131a hcase330a hcase330b hcase321a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase40 hcase41 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase421a hcase421b hcase300a hcase300b hcase131a hcase331a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase32 hcase40 hcase41 hcase43 hcase44
                    omega
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase110b hcase120b hcase421a hcase421b hcase100b hcase00 hcase01 hcase02 hcase03 hcase04 hcase13 hcase14 hcase32 hcase33 hcase40 hcase41 hcase43 hcase44
                omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110b hcase120b hcase421a hcase421b hcase301a hcase301b hcase101a hcase140b hcase130b hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase40 hcase41 hcase43 hcase44
                    omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase421a hcase421b hcase301a hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase330b hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase40 hcase41 hcase43 hcase44
                      omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase421a hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase331a hcase331b hcase400b hcase430b hcase440b hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase41
                            omega
                          ·
                            rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                            ·
                              clear hn4 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340b hcase110b hcase120b hcase421a hcase421b hcase101a hcase140a hcase140b hcase131a hcase331a hcase400a hcase400b hcase430a hcase430b hcase441a hcase441b hcase000b hcase01 hcase02 hcase03 hcase04 hcase32 hcase41
                              omega
                            ·
                              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                              ·
                                clear hn4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase421a hcase101a hcase140a hcase140b hcase131a hcase331a hcase400b hcase430b hcase441a hcase001a hcase040b hcase01 hcase02 hcase03 hcase32 hcase41
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase120a hcase120b hcase421a hcase421b hcase301a hcase301b hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase331a hcase331b hcase400a hcase400b hcase430a hcase430b hcase441a hcase441b hcase001a hcase001b hcase041a hcase01 hcase02 hcase03 hcase32 hcase41
                                omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase120a hcase120b hcase421a hcase301a hcase301b hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase331a hcase331b hcase400a hcase400b hcase431a hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase41 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase120a hcase120b hcase421a hcase301a hcase301b hcase101a hcase101b hcase140a hcase140b hcase131a hcase131b hcase331a hcase331b hcase401a hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase41 hcase43 hcase44
                        omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110b hcase120b hcase421a hcase421b hcase301a hcase301b hcase101a hcase141a hcase130b hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase40 hcase41 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase120a hcase120b hcase421a hcase421b hcase301a hcase101a hcase101b hcase131a hcase00 hcase01 hcase02 hcase03 hcase04 hcase32 hcase33 hcase40 hcase41 hcase43 hcase44
                    omega
        ·
          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
          ·
            rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110b hcase121a hcase030a hcase030b hcase000a hcase000b hcase100b hcase130b hcase01 hcase02 hcase04 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase110a hcase110b hcase121a hcase030a hcase030b hcase000a hcase000b hcase100b hcase131a hcase140b hcase01 hcase02 hcase04 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut1 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110b hcase121a hcase030a hcase030b hcase000a hcase000b hcase100b hcase131a hcase330b hcase01 hcase02 hcase04 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase000a hcase000b hcase100a hcase100b hcase131a hcase331a hcase01 hcase02 hcase04 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase121b hcase030b hcase000b hcase040b hcase01 hcase02 hcase13 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase000a hcase000b hcase101a hcase101b hcase041a hcase01 hcase02 hcase13 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110b hcase121a hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase100b hcase130b hcase01 hcase02 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase110a hcase110b hcase121a hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase100b hcase131a hcase140b hcase01 hcase02 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut1 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110b hcase121a hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase100b hcase131a hcase330b hcase01 hcase02 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase100a hcase100b hcase131a hcase331a hcase01 hcase02 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase330a hcase330b hcase300a hcase300b hcase400a hcase400b hcase420a hcase420b hcase410a hcase410b hcase440b hcase01 hcase02 hcase13 hcase14 hcase32 hcase43
                              omega
                            ·
                              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                              ·
                                clear hn4 hsum_nat1 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase121b hcase030b hcase001a hcase040b hcase330a hcase330b hcase300a hcase300b hcase400b hcase420b hcase410b hcase441a hcase430b hcase01 hcase02 hcase13 hcase14 hcase32
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase330a hcase330b hcase300a hcase300b hcase400b hcase420b hcase410b hcase441a hcase431a hcase01 hcase02 hcase13 hcase14 hcase32
                                omega
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase330a hcase330b hcase300a hcase300b hcase400b hcase420a hcase420b hcase411a hcase430b hcase440b hcase01 hcase02 hcase13 hcase14 hcase32
                                omega
                              ·
                                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                                ·
                                  clear hn4 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340a hcase340b hcase311a hcase110a hcase110b hcase121a hcase030b hcase001a hcase040b hcase101a hcase330a hcase330b hcase300a hcase300b hcase400b hcase420a hcase420b hcase411a hcase430b hcase441a hcase130b hcase01 hcase02 hcase14 hcase32
                                  omega
                                ·
                                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                                  ·
                                    clear hn4 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340a hcase340b hcase311a hcase110a hcase110b hcase121a hcase030b hcase001a hcase040b hcase101a hcase330a hcase330b hcase300a hcase300b hcase400b hcase420a hcase420b hcase411a hcase430b hcase441a hcase131a hcase140b hcase01 hcase02 hcase32
                                    omega
                                  ·
                                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase330a hcase330b hcase300a hcase300b hcase400a hcase400b hcase420a hcase420b hcase411a hcase411b hcase430a hcase430b hcase441a hcase441b hcase131a hcase141a hcase01 hcase02 hcase32
                                    omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase330a hcase330b hcase300a hcase300b hcase400a hcase400b hcase420a hcase420b hcase411a hcase431a hcase01 hcase02 hcase13 hcase14 hcase32 hcase44
                              omega
                        ·
                          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                          ·
                            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                            ·
                              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                              ·
                                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                                ·
                                  clear hn4 hsum_nat0 hsum_nat1 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase330a hcase330b hcase300a hcase300b hcase400b hcase421a hcase130a hcase130b hcase140a hcase140b hcase430b hcase440b hcase01 hcase02 hcase32 hcase41
                                  omega
                                ·
                                  clear hn4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase030b hcase001a hcase040b hcase101a hcase330a hcase330b hcase300a hcase300b hcase400b hcase421a hcase130b hcase140b hcase430b hcase441a hcase01 hcase02 hcase32 hcase41
                                  omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase330a hcase330b hcase300a hcase300b hcase400a hcase400b hcase421a hcase130a hcase130b hcase140a hcase140b hcase431a hcase01 hcase02 hcase32 hcase41 hcase44
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase330a hcase330b hcase300b hcase400a hcase400b hcase421a hcase421b hcase130b hcase01 hcase02 hcase32 hcase41 hcase43 hcase44
                              omega
                          ·
                            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase330b hcase300b hcase400a hcase400b hcase421a hcase421b hcase320b hcase01 hcase02 hcase14 hcase41 hcase43 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase330a hcase330b hcase300b hcase400a hcase400b hcase421a hcase421b hcase131a hcase321a hcase01 hcase02 hcase14 hcase41 hcase43 hcase44
                              omega
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase330a hcase330b hcase300b hcase320b hcase01 hcase02 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase330b hcase300a hcase300b hcase401a hcase401b hcase321a hcase01 hcase02 hcase13 hcase14 hcase41 hcase42 hcase43 hcase44
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase330b hcase301a hcase01 hcase02 hcase13 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase130b hcase01 hcase02 hcase14 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase331a hcase131a hcase140a hcase140b hcase300b hcase01 hcase02 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase331a hcase331b hcase131a hcase131b hcase140a hcase140b hcase301a hcase301b hcase440b hcase01 hcase02 hcase32 hcase40 hcase41 hcase42 hcase43
                            omega
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340a hcase340b hcase311a hcase110a hcase110b hcase121a hcase030b hcase001a hcase040b hcase101a hcase331a hcase331b hcase131a hcase140b hcase301a hcase301b hcase441a hcase430b hcase400b hcase01 hcase02 hcase32 hcase41 hcase42
                                omega
                              ·
                                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                                ·
                                  clear hn4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340b hcase311a hcase110a hcase110b hcase121a hcase030b hcase001a hcase040b hcase101a hcase331a hcase131a hcase140a hcase140b hcase301a hcase441a hcase430b hcase401a hcase320b hcase01 hcase02 hcase41 hcase42
                                  omega
                                ·
                                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase331a hcase131a hcase131b hcase140a hcase140b hcase301a hcase441a hcase441b hcase430a hcase430b hcase401a hcase401b hcase321a hcase01 hcase02 hcase41 hcase42
                                  omega
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat3 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase110a hcase110b hcase121a hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase331a hcase331b hcase131a hcase140a hcase140b hcase441a hcase431a hcase400b hcase01 hcase02 hcase32 hcase41 hcase42
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase101b hcase331a hcase331b hcase131a hcase131b hcase140a hcase140b hcase301a hcase301b hcase441a hcase441b hcase431a hcase401a hcase01 hcase02 hcase32 hcase41 hcase42
                                omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase030a hcase030b hcase001a hcase001b hcase040a hcase040b hcase101a hcase331a hcase331b hcase131a hcase141a hcase01 hcase02 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase121b hcase030a hcase030b hcase001a hcase001b hcase041a hcase01 hcase02 hcase10 hcase13 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase110a hcase110b hcase121a hcase121b hcase031a hcase00 hcase01 hcase02 hcase04 hcase10 hcase13 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
      ·
        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
        ·
          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase111a hcase000a hcase000b hcase100b hcase130b hcase120b hcase01 hcase02 hcase03 hcase04 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase111a hcase000a hcase000b hcase100b hcase130b hcase121a hcase01 hcase02 hcase03 hcase04 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase111a hcase000a hcase000b hcase100b hcase131a hcase120a hcase120b hcase140b hcase01 hcase02 hcase03 hcase04 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase000a hcase000b hcase100b hcase131a hcase120b hcase320b hcase330b hcase01 hcase02 hcase03 hcase04 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase000a hcase000b hcase100a hcase100b hcase131a hcase120a hcase120b hcase320a hcase320b hcase331a hcase01 hcase02 hcase03 hcase04 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase000a hcase000b hcase100a hcase100b hcase131a hcase120a hcase120b hcase321a hcase01 hcase02 hcase03 hcase04 hcase30 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase111a hcase000a hcase000b hcase100b hcase131a hcase121a hcase140b hcase01 hcase02 hcase03 hcase04 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase111a hcase000a hcase000b hcase100a hcase100b hcase131a hcase121a hcase141a hcase01 hcase02 hcase03 hcase04 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase000b hcase040b hcase030b hcase01 hcase02 hcase12 hcase13 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase000a hcase000b hcase101a hcase101b hcase040a hcase040b hcase031a hcase01 hcase02 hcase12 hcase13 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase000a hcase000b hcase101a hcase101b hcase041a hcase01 hcase02 hcase03 hcase12 hcase13 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase001a hcase001b hcase130a hcase130b hcase030a hcase030b hcase040a hcase040b hcase120a hcase120b hcase300a hcase300b hcase320a hcase320b hcase400a hcase400b hcase440b hcase01 hcase02 hcase10 hcase14 hcase33 hcase41 hcase42 hcase43
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                              ·
                                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                                ·
                                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase111a hcase001a hcase001b hcase130b hcase030a hcase030b hcase040a hcase040b hcase120b hcase300a hcase300b hcase320a hcase320b hcase400a hcase400b hcase441a hcase441b hcase420a hcase420b hcase410a hcase410b hcase430a hcase430b hcase100b hcase01 hcase02 hcase14 hcase33
                                  omega
                                ·
                                  clear hn4 hsum_nat1 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase001a hcase130a hcase130b hcase030b hcase040b hcase120a hcase120b hcase300a hcase300b hcase320a hcase320b hcase400b hcase441a hcase420b hcase410b hcase430b hcase01 hcase02 hcase14 hcase33
                                  omega
                              ·
                                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                                ·
                                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase111a hcase001a hcase001b hcase130b hcase030a hcase030b hcase040a hcase040b hcase120b hcase300a hcase300b hcase320a hcase320b hcase400a hcase400b hcase441a hcase441b hcase420a hcase420b hcase410a hcase410b hcase431a hcase431b hcase100b hcase01 hcase02 hcase14 hcase33
                                  omega
                                ·
                                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase001a hcase001b hcase130a hcase130b hcase030a hcase030b hcase040a hcase040b hcase120a hcase120b hcase300a hcase300b hcase320a hcase320b hcase400b hcase441a hcase420b hcase410b hcase431a hcase01 hcase02 hcase14 hcase33
                                  omega
                            ·
                              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                              ·
                                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                                ·
                                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase111a hcase001a hcase001b hcase130b hcase030a hcase030b hcase040a hcase040b hcase120a hcase120b hcase300a hcase300b hcase320a hcase320b hcase400a hcase400b hcase441a hcase441b hcase420a hcase420b hcase430a hcase430b hcase100b hcase01 hcase02 hcase14 hcase33
                                  omega
                                ·
                                  clear hn4 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340a hcase340b hcase311a hcase111a hcase001a hcase130b hcase030b hcase040b hcase120a hcase120b hcase300a hcase300b hcase320a hcase320b hcase400b hcase441a hcase420a hcase420b hcase411a hcase430b hcase101a hcase01 hcase02 hcase14 hcase33
                                  omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase001a hcase001b hcase130a hcase130b hcase030a hcase030b hcase040a hcase040b hcase120a hcase120b hcase300a hcase300b hcase320a hcase320b hcase400a hcase400b hcase441a hcase441b hcase420a hcase420b hcase411a hcase431a hcase01 hcase02 hcase10 hcase14 hcase33
                                omega
                          ·
                            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase111a hcase001a hcase001b hcase130b hcase030a hcase030b hcase040a hcase040b hcase120a hcase120b hcase300a hcase300b hcase320a hcase320b hcase400a hcase400b hcase441a hcase441b hcase100b hcase01 hcase02 hcase14 hcase33 hcase41 hcase43
                              omega
                            ·
                              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                              ·
                                clear hn4 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340a hcase340b hcase311a hcase111a hcase001a hcase130b hcase030b hcase040b hcase120a hcase120b hcase300a hcase300b hcase320a hcase320b hcase400b hcase441a hcase421a hcase101a hcase430b hcase01 hcase02 hcase14 hcase33 hcase41
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase001a hcase001b hcase130a hcase130b hcase030a hcase030b hcase040a hcase040b hcase120a hcase120b hcase300a hcase300b hcase320a hcase320b hcase400a hcase400b hcase441a hcase441b hcase421a hcase101a hcase101b hcase431a hcase01 hcase02 hcase14 hcase33 hcase41
                                omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase130a hcase130b hcase030a hcase030b hcase040a hcase040b hcase120a hcase120b hcase300b hcase320b hcase01 hcase02 hcase10 hcase14 hcase33 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase001a hcase001b hcase130b hcase030a hcase030b hcase040a hcase040b hcase120a hcase120b hcase300a hcase300b hcase01 hcase02 hcase10 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase130a hcase130b hcase030a hcase030b hcase040a hcase040b hcase120a hcase120b hcase301a hcase330b hcase01 hcase02 hcase10 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase130b hcase030a hcase030b hcase040a hcase040b hcase120a hcase120b hcase301a hcase331a hcase01 hcase02 hcase10 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase111a hcase001a hcase001b hcase130b hcase030a hcase030b hcase040a hcase040b hcase121a hcase330a hcase330b hcase140b hcase300a hcase300b hcase400a hcase400b hcase430a hcase430b hcase100b hcase01 hcase02 hcase32 hcase41 hcase42 hcase44
                              omega
                            ·
                              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase001a hcase001b hcase130a hcase130b hcase030a hcase030b hcase040a hcase040b hcase330a hcase330b hcase140a hcase140b hcase300a hcase300b hcase400b hcase430b hcase101a hcase101b hcase440b hcase01 hcase02 hcase32 hcase41 hcase42
                                omega
                              ·
                                clear hn4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase111a hcase001a hcase130b hcase030b hcase040b hcase121a hcase330a hcase330b hcase140b hcase300a hcase300b hcase400b hcase430b hcase101a hcase441a hcase01 hcase02 hcase32 hcase41 hcase42
                                omega
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase001a hcase001b hcase130a hcase130b hcase030a hcase030b hcase040a hcase040b hcase121a hcase121b hcase330a hcase330b hcase140a hcase140b hcase300a hcase300b hcase400a hcase400b hcase431a hcase431b hcase440b hcase01 hcase02 hcase10 hcase32 hcase41 hcase42
                              omega
                            ·
                              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase111a hcase001a hcase001b hcase130b hcase030a hcase030b hcase040a hcase040b hcase121a hcase330a hcase330b hcase140b hcase300a hcase300b hcase400a hcase400b hcase431a hcase431b hcase441a hcase441b hcase100b hcase01 hcase02 hcase32 hcase41 hcase42
                                omega
                              ·
                                clear hn4 hsum_nat0 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase111a hcase001a hcase001b hcase130b hcase030a hcase030b hcase040a hcase040b hcase121a hcase330a hcase330b hcase140b hcase300a hcase300b hcase400b hcase431a hcase441a hcase101a hcase01 hcase02 hcase32 hcase41 hcase42
                                omega
                        ·
                          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase130a hcase130b hcase030a hcase030b hcase040a hcase040b hcase121a hcase121b hcase330a hcase330b hcase140a hcase140b hcase300b hcase320b hcase01 hcase02 hcase10 hcase41 hcase42 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase130b hcase030a hcase030b hcase040a hcase040b hcase121a hcase121b hcase330a hcase330b hcase140a hcase140b hcase300b hcase321a hcase01 hcase02 hcase10 hcase41 hcase42 hcase43 hcase44
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase130a hcase130b hcase030a hcase030b hcase040a hcase040b hcase121a hcase121b hcase330b hcase140a hcase140b hcase301a hcase01 hcase02 hcase10 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase130b hcase030a hcase030b hcase040a hcase040b hcase121a hcase121b hcase330a hcase330b hcase300b hcase01 hcase02 hcase10 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase130a hcase130b hcase030a hcase030b hcase040a hcase040b hcase121a hcase121b hcase330b hcase141a hcase141b hcase301a hcase01 hcase02 hcase10 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase001a hcase001b hcase130b hcase030a hcase030b hcase040a hcase040b hcase121a hcase121b hcase01 hcase02 hcase10 hcase14 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase001a hcase001b hcase130a hcase130b hcase030a hcase030b hcase041a hcase01 hcase02 hcase10 hcase12 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase001a hcase001b hcase130a hcase130b hcase031a hcase01 hcase02 hcase04 hcase10 hcase12 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase040a hcase040b hcase330b hcase320b hcase300b hcase01 hcase02 hcase03 hcase10 hcase12 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase040a hcase040b hcase330b hcase320b hcase301a hcase01 hcase02 hcase03 hcase10 hcase12 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase330b hcase321a hcase01 hcase02 hcase03 hcase10 hcase12 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase111a hcase001a hcase001b hcase131a hcase040a hcase040b hcase331a hcase331b hcase400a hcase400b hcase430a hcase430b hcase100b hcase140b hcase01 hcase02 hcase03 hcase12 hcase30 hcase32 hcase41 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase131a hcase040a hcase040b hcase331a hcase400a hcase400b hcase430a hcase430b hcase100a hcase100b hcase01 hcase02 hcase03 hcase12 hcase30 hcase32 hcase41 hcase42 hcase44
                        omega
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase001a hcase001b hcase131a hcase040a hcase040b hcase400b hcase430b hcase101a hcase101b hcase140a hcase140b hcase030a hcase030b hcase440b hcase01 hcase02 hcase12 hcase30 hcase32 hcase41 hcase42
                            omega
                          ·
                            clear hn4 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340a hcase340b hcase311a hcase111a hcase001a hcase131a hcase040b hcase331a hcase331b hcase400b hcase430b hcase101a hcase140b hcase030b hcase441a hcase01 hcase02 hcase12 hcase30 hcase32 hcase41 hcase42
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase331a hcase331b hcase400a hcase400b hcase430a hcase430b hcase101a hcase101b hcase140a hcase140b hcase031a hcase01 hcase02 hcase12 hcase30 hcase32 hcase41 hcase42 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase111a hcase001a hcase001b hcase131a hcase040a hcase040b hcase331a hcase331b hcase400a hcase400b hcase430a hcase430b hcase101a hcase141a hcase01 hcase02 hcase03 hcase12 hcase30 hcase32 hcase41 hcase42 hcase44
                        omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase111a hcase001a hcase001b hcase131a hcase040a hcase040b hcase331a hcase331b hcase400a hcase400b hcase431a hcase431b hcase140b hcase100b hcase01 hcase02 hcase03 hcase12 hcase30 hcase32 hcase41 hcase42 hcase44
                        omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase331a hcase331b hcase400a hcase400b hcase431a hcase431b hcase140a hcase140b hcase101a hcase101b hcase440b hcase01 hcase02 hcase03 hcase12 hcase30 hcase32 hcase41 hcase42
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase111a hcase001a hcase001b hcase131a hcase040a hcase040b hcase331a hcase331b hcase400b hcase431a hcase140b hcase101a hcase441a hcase01 hcase02 hcase03 hcase12 hcase30 hcase32 hcase41 hcase42
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase131a hcase040a hcase040b hcase331a hcase400a hcase400b hcase431a hcase431b hcase01 hcase02 hcase03 hcase10 hcase12 hcase30 hcase32 hcase41 hcase42 hcase44
                      omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut11 hcut6 hcut46 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase131a hcase040a hcase040b hcase331a hcase401a hcase401b hcase300b hcase01 hcase02 hcase03 hcase10 hcase12 hcase14 hcase32 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340b hcase311a hcase111a hcase001a hcase001b hcase131a hcase040a hcase040b hcase331a hcase301a hcase320b hcase430a hcase430b hcase100b hcase01 hcase02 hcase03 hcase12 hcase14 hcase41 hcase42 hcase44
                          omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase401a hcase301a hcase301b hcase320a hcase320b hcase430b hcase101a hcase101b hcase440b hcase01 hcase02 hcase03 hcase12 hcase14 hcase41 hcase42
                            omega
                          ·
                            clear hn4 hcut1 hcut59 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut38 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut11 hcut6 hcut46 hcut28 hcut15 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase340b hcase311a hcase111a hcase001a hcase131a hcase040b hcase331a hcase401a hcase301a hcase320b hcase430b hcase101a hcase441a hcase01 hcase02 hcase03 hcase12 hcase14 hcase41 hcase42
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase011a hcase011b hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase331a hcase331b hcase401a hcase301a hcase301b hcase320a hcase320b hcase431a hcase01 hcase02 hcase03 hcase10 hcase12 hcase14 hcase41 hcase42 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase011a hcase011b hcase340a hcase340b hcase311a hcase111a hcase111b hcase001a hcase001b hcase131a hcase131b hcase040a hcase040b hcase331a hcase401a hcase401b hcase301a hcase321a hcase01 hcase02 hcase03 hcase10 hcase12 hcase14 hcase41 hcase42 hcase43 hcase44
                      omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase340a hcase340b hcase311a hcase311b hcase111a hcase111b hcase001a hcase001b hcase131a hcase131b hcase041a hcase01 hcase02 hcase03 hcase10 hcase12 hcase14 hcase30 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
  ·
    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
    ·
      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
      ·
        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
        ·
          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
          ·
            clear hn4 hsum_nat1 hsum_nat3 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase040b hcase030b hcase000b hcase020b hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase341a hcase341b hcase040a hcase040b hcase030a hcase030b hcase000a hcase000b hcase021a hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
        ·
          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
          ·
            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase040a hcase040b hcase030a hcase030b hcase001a hcase001b hcase020a hcase020b hcase440b hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut61 hcut64 hcut42 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase011a hcase040b hcase030b hcase001a hcase020b hcase441a hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase341a hcase341b hcase040a hcase040b hcase030a hcase030b hcase001a hcase001b hcase021a hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase341a hcase341b hcase040a hcase040b hcase031a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut1 hcut59 hcut2 hcut33 hcut68 hcut57 hcut22 hcut17 hcut37 hcut55 hcut43 hcut20 hcut60 hcut38 hcut61 hcut64 hcut42 hcut5 hcut14 hcut13 hcut69 hcut19 hcut7 hcut0 hcut11 hcut6 hcut46 hcut28 hcut15 hcut67 hcut66 hcut25 hcut58 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase011a hcase341a hcase341b hcase041a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
      omega

#print axioms symbolic_v2_mask959_integer_shard003
end Jsp404.SixExactFloorKernel
