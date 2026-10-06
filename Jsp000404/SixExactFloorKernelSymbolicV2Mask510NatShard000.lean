import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask510_integer_shard000 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut3 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 2))
    (hcut57 : (s10 + s11 + u10 + u11 + 1) + 1 ≤ (n))
    (hcut85 : (s01 + s30 + s31 + s34 + s42 + s43 + u01 + u30 + u31 + u34 + u42 + u43) + 1 ≤ (n + 1))
    (hcut13 : (s03 + u03) + 1 ≤ (s13 + 2))
    (hcut36 : (s02 + s10 + s14 + u02 + u10 + u14) + 1 ≤ (n))
    (hcut72 : (s02 + s33 + u02 + u33) + 1 ≤ (s12 + 2))
    (hcut2 : (s40 + s41 + s42 + u40 + u41 + u42) + 1 ≤ (s10 + 3))
    (hcut5 : (s41 + u41) + 1 ≤ (s31 + 2))
    (hcut73 : (s12 + s13 + s14 + s31 + u12 + u13 + u14 + u31 + 1) + 1 ≤ (n))
    (hcut25 : (s01 + s30 + s34 + u01 + u30 + u34) + 1 ≤ (n))
    (hcut33 : (s10 + s43 + s44 + u10 + u43 + u44) + 1 ≤ (n + 2))
    (hcut9 : (s13 + s30 + s31 + u13 + u30 + u31 + 2) + 1 ≤ (n))
    (hcut68 : (s02 + s13 + s30 + u02 + u13 + u30 + 2) + 1 ≤ (n))
    (hcut4 : (s00 + s02 + s03 + s04 + s32 + s33 + s40 + s41 + s44 + u00 + u02 + u03 + u04 + u32 + u33 + u40 + u41 + u44) + 1 ≤ (2 * n + 2))
    (hcut77 : (s12 + s13 + s14 + s30 + s31 + u12 + u13 + u14 + u30 + u31) + 1 ≤ (n))
    (hcut45 : (s12 + s40 + u12 + u40 + 2) + 1 ≤ (n))
    (hcut53 : (s32 + s33 + s40 + u32 + u33 + u40 + 1) + 1 ≤ (n))
    (hcut29 : (s02 + s13 + s33 + u02 + u13 + u33 + 3) + 1 ≤ (n))
    (hcut15 : (s12 + s31 + u12 + u31 + 2) + 1 ≤ (n))
    (hcut62 : (s40 + s42 + s44 + u40 + u42 + u44) + 1 ≤ (n + 1))
    (hcut54 : (s40 + s43 + s44 + u40 + u43 + u44) + 1 ≤ (n + 1))
    (hcut69 : (s10 + s13 + s14 + s40 + s41 + s44 + u10 + u13 + u14 + u40 + u41 + u44) + 1 ≤ (2 * n))
    (hcut83 : (s12 + s13 + s14 + s31 + s32 + u12 + u13 + u14 + u31 + u32) + 1 ≤ (n))
    (hcut24 : (s03 + s04 + s10 + s12 + u03 + u04 + u10 + u12) + 1 ≤ (n + 1))
    (hcut52 : (s13 + u13) + 1 ≤ (s34 + 1))
    (hcut65 : (s01 + s34 + s42 + s43 + u01 + u34 + u42 + u43) + 1 ≤ (n))
    (hcut39 : (s14 + s32 + u14 + u32 + 3) + 1 ≤ (n))
    (hcut61 : (s04 + s10 + s11 + u04 + u10 + u11) + 1 ≤ (n))
    (hcut48 : (s12 + s30 + s31 + s32 + u12 + u30 + u31 + u32 + 1) + 1 ≤ (n))
    (hcut47 : (s01 + s34 + u01 + u34) + 1 ≤ (s44 + 2))
    (hcut58 : (s10 + s14 + s40 + s41 + s44 + u10 + u14 + u40 + u41 + u44 + 1) + 1 ≤ (2 * n))
    (hcut8 : (s11 + u11) + 1 ≤ (s32 + 2))
    (hcut75 : (s03 + s04 + s12 + s32 + u03 + u04 + u12 + u32) + 1 ≤ (n))
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
    (hcase000a : s00 = 0)
    (hcase000b : u00 = 0)
    : False := by
  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
  ·
    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
    ·
      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
      ·
        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase030b hcase040b hcase010b hcase00 hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
      ·
        rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
        ·
          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase030b hcase040b hcase011a hcase120a hcase120b hcase020a hcase020b hcase310b hcase320b hcase00 hcase10 hcase11 hcase13 hcase14 hcase30 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut2 hcut5 hcut73 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase030b hcase040b hcase011a hcase120b hcase020a hcase020b hcase310b hcase321a hcase00 hcase10 hcase11 hcase13 hcase14 hcase30 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase030b hcase040b hcase011a hcase120a hcase120b hcase020b hcase00 hcase10 hcase11 hcase13 hcase14 hcase30 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase030a hcase030b hcase040a hcase040b hcase011a hcase120a hcase120b hcase021a hcase00 hcase10 hcase11 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
        ·
          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase030b hcase040b hcase011a hcase121a hcase121b hcase310b hcase320b hcase00 hcase02 hcase10 hcase11 hcase13 hcase14 hcase30 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase030b hcase040b hcase011a hcase310a hcase310b hcase321a hcase020b hcase330b hcase00 hcase10 hcase11 hcase13 hcase14 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase030b hcase040b hcase011a hcase121a hcase121b hcase310b hcase321a hcase020b hcase331a hcase00 hcase10 hcase11 hcase13 hcase14 hcase30 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase030a hcase030b hcase040a hcase040b hcase011a hcase121a hcase121b hcase310a hcase310b hcase321a hcase321b hcase021a hcase00 hcase10 hcase11 hcase13 hcase14 hcase30 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            clear hn4 hsum_nat1 hsum_nat4 hcut3 hcut57 hcut13 hcut36 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase030b hcase040b hcase011a hcase121a hcase00 hcase02 hcase10 hcase11 hcase13 hcase14 hcase30 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
    ·
      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
      ·
        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
        ·
          rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000a hcase000b hcase030a hcase030b hcase041a hcase041b hcase110b hcase100b hcase120b hcase130b hcase00 hcase01 hcase02 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000a hcase000b hcase030a hcase030b hcase041a hcase041b hcase110b hcase100b hcase120b hcase131a hcase140b hcase00 hcase01 hcase02 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000a hcase000b hcase030a hcase030b hcase041a hcase041b hcase110b hcase100b hcase120a hcase120b hcase131a hcase141a hcase00 hcase01 hcase02 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase030a hcase030b hcase041a hcase110a hcase110b hcase100a hcase100b hcase010b hcase020b hcase00 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase030a hcase030b hcase041a hcase110a hcase110b hcase100a hcase100b hcase121a hcase121b hcase010a hcase010b hcase021a hcase00 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase030a hcase030b hcase041a hcase110a hcase110b hcase100a hcase100b hcase121a hcase121b hcase011a hcase00 hcase02 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase030a hcase030b hcase041a hcase110a hcase110b hcase020b hcase010b hcase00 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase030a hcase030b hcase041a hcase110a hcase110b hcase101a hcase101b hcase020a hcase020b hcase011a hcase00 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase030a hcase030b hcase041a hcase110a hcase110b hcase101a hcase101b hcase021a hcase00 hcase01 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
      ·
        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000a hcase000b hcase030a hcase030b hcase041a hcase041b hcase320b hcase00 hcase01 hcase02 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
          ·
            clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase030a hcase030b hcase041a hcase111a hcase111b hcase010b hcase00 hcase02 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase030a hcase030b hcase041a hcase111a hcase111b hcase321a hcase321b hcase011a hcase00 hcase02 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
  ·
    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
    ·
      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
      ·
        rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
        ·
          clear hn4 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase031a hcase020b hcase040b hcase010b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase031a hcase020a hcase020b hcase040a hcase040b hcase011a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase031a hcase020a hcase020b hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut57 hcut85 hcut13 hcut36 hcut72 hcut2 hcut5 hcut73 hcut25 hcut33 hcut9 hcut68 hcut4 hcut77 hcut45 hcut53 hcut29 hcut15 hcut62 hcut54 hcut69 hcut83 hcut24 hcut52 hcut65 hcut39 hcut61 hcut48 hcut47 hcut58 hcut8 hcut75 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase031a hcase021a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega

#print axioms symbolic_v2_mask510_integer_shard000
end Jsp404.SixExactFloorKernel
