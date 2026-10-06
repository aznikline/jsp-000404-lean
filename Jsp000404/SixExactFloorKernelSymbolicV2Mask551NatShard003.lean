import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask551_integer_shard003 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut5 : (s02 + s42 + u02 + u42) + 1 ≤ (s32 + 2))
    (hcut15 : (s13 + s40 + u13 + u40) + 1 ≤ (n))
    (hcut36 : (s43 + u43 + 1) + 1 ≤ (n))
    (hcut28 : (s33 + u33 + 2) + 1 ≤ (n))
    (hcut2 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 1))
    (hcut23 : (s01 + s03 + s04 + s40 + s44 + u01 + u03 + u04 + u40 + u44) + 1 ≤ (2 * n))
    (hcut12 : (s30 + u30 + 2) + 1 ≤ (n))
    (hcut26 : (s03 + s11 + s14 + s31 + u03 + u11 + u14 + u31 + 1) + 1 ≤ (n))
    (hcut32 : (s30 + s33 + s34 + u30 + u33 + u34 + 1) + 1 ≤ (n))
    (hcut43 : (s03 + s10 + s11 + s14 + s31 + s32 + u03 + u10 + u11 + u14 + u31 + u32) + 1 ≤ (n + 1))
    (hcut3 : (s03 + s32 + s41 + u03 + u32 + u41) + 1 ≤ (s13 + 2))
    (hcut18 : (s12 + u12) + 1 ≤ (s31 + 2))
    (hcut11 : (s11 + s31 + u11 + u31 + 2) + 1 ≤ (n))
    (hcut4 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut9 : (s40 + s41 + s42 + s43 + u40 + u41 + u42 + u43) + 1 ≤ (n))
    (hcut33 : (s12 + s13 + s14 + s30 + u12 + u13 + u14 + u30) + 1 ≤ (n + 1))
    (hcut35 : (s03 + s10 + s11 + s14 + s31 + u03 + u10 + u11 + u14 + u31) + 1 ≤ (n))
    (hcut29 : (s00 + s04 + s40 + s44 + u00 + u04 + u40 + u44) + 1 ≤ (2 * n))
    (hcut38 : (s00 + s04 + s34 + s43 + u00 + u04 + u34 + u43) + 1 ≤ (2 * n))
    (hcut46 : (s00 + s01 + s43 + s44 + u00 + u01 + u43 + u44) + 1 ≤ (n + 2))
    (hcut45 : (s01 + s43 + s44 + u01 + u43 + u44) + 1 ≤ (n + 1))
    (hcut16 : (s10 + s11 + s31 + u10 + u11 + u31 + 1) + 1 ≤ (n))
    (hcut1 : (s32 + s33 + s34 + s40 + s41 + u32 + u33 + u34 + u40 + u41) + 1 ≤ (n + 1))
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
    (hcase020a : s02 = 0)
    (hcase020b : u02 = 0)
    (hcase030a : s03 = 0)
    (hcase030b : u03 = 0)
    (hcase001a : 1 ≤ s00)
    (hcase001b : u00 = 1)
    (hcase041a : 1 ≤ s04)
    (hcase041b : u04 = 1)
    : False := by
  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
  ·
    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
    ·
      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
      ·
        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
        ·
          rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase340a hcase340b hcase110b hcase130b hcase120b hcase100b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330b hcase340b hcase110a hcase110b hcase130a hcase130b hcase120a hcase120b hcase100a hcase100b hcase320b hcase300b hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330b hcase340b hcase110a hcase110b hcase130b hcase120b hcase100b hcase141a hcase320b hcase301a hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase130b hcase120a hcase120b hcase100a hcase100b hcase141a hcase141b hcase00 hcase01 hcase02 hcase03 hcase04 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330b hcase340b hcase110a hcase110b hcase130a hcase130b hcase120a hcase120b hcase320b hcase300b hcase00 hcase01 hcase02 hcase03 hcase04 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase130a hcase130b hcase120a hcase120b hcase101a hcase101b hcase320a hcase320b hcase301a hcase301b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330b hcase340b hcase110a hcase110b hcase130b hcase120b hcase101a hcase320b hcase301a hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase130b hcase120a hcase120b hcase101a hcase101b hcase00 hcase01 hcase02 hcase03 hcase04 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase130a hcase130b hcase310b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase14 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase130a hcase130b hcase121a hcase121b hcase311a hcase311b hcase100a hcase100b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase130b hcase121a hcase311a hcase100b hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase130a hcase130b hcase121a hcase121b hcase311a hcase311b hcase101a hcase101b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase130b hcase121a hcase311a hcase101a hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
        ·
          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase131a hcase131b hcase100a hcase100b hcase320a hcase320b hcase300a hcase300b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330b hcase340b hcase110a hcase110b hcase131a hcase131b hcase100a hcase100b hcase320b hcase300b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase131a hcase131b hcase100a hcase100b hcase320a hcase320b hcase301a hcase301b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase340a hcase340b hcase110b hcase131a hcase100b hcase320a hcase320b hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330b hcase340b hcase110a hcase110b hcase131a hcase131b hcase100a hcase100b hcase321a hcase310b hcase300b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase131a hcase131b hcase100a hcase100b hcase321a hcase321b hcase310a hcase310b hcase301a hcase301b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase340a hcase340b hcase110b hcase131a hcase100b hcase321a hcase321b hcase310a hcase310b hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase131a hcase131b hcase100a hcase100b hcase321a hcase321b hcase311a hcase311b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330b hcase340b hcase110a hcase110b hcase131a hcase131b hcase100a hcase100b hcase321a hcase311a hcase300b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut4 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330b hcase340b hcase110a hcase110b hcase131a hcase100a hcase100b hcase321a hcase311a hcase301a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase131a hcase131b hcase101a hcase101b hcase300a hcase300b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330b hcase340b hcase110a hcase110b hcase131a hcase131b hcase300b hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330b hcase340b hcase110a hcase110b hcase131a hcase131b hcase101a hcase101b hcase301a hcase310b hcase320b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase131a hcase131b hcase101a hcase101b hcase301a hcase301b hcase310a hcase310b hcase321a hcase321b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330b hcase340b hcase110a hcase110b hcase131a hcase101a hcase301a hcase310a hcase310b hcase321a hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase110a hcase110b hcase131a hcase131b hcase101a hcase101b hcase301a hcase301b hcase311a hcase311b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330b hcase340b hcase110a hcase110b hcase131a hcase101a hcase301a hcase311a hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
      ·
        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase111a hcase111b hcase300a hcase300b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase12 hcase13 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330b hcase340b hcase300b hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase12 hcase13 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase111a hcase111b hcase301a hcase301b hcase320a hcase320b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase12 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330b hcase340b hcase111a hcase301a hcase320b hcase141a hcase100b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330b hcase340b hcase111a hcase301a hcase320b hcase141a hcase101a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase340a hcase340b hcase111a hcase111b hcase301a hcase301b hcase130b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase12 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase340a hcase340b hcase111a hcase111b hcase301a hcase301b hcase321a hcase321b hcase131a hcase131b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330b hcase340b hcase111a hcase301a hcase321a hcase131a hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
    ·
      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
      ·
        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hsum_nat0 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase320a hcase320b hcase300a hcase300b hcase420b hcase410b hcase400b hcase010a hcase010b hcase430b hcase440b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase320a hcase320b hcase300a hcase300b hcase420b hcase410b hcase400b hcase010a hcase010b hcase430b hcase441a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14
                        omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase330b hcase341a hcase310b hcase320b hcase300b hcase420a hcase420b hcase410a hcase410b hcase400a hcase400b hcase010b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase320a hcase320b hcase300a hcase300b hcase420a hcase420b hcase410a hcase410b hcase400a hcase400b hcase011a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase43 hcase44
                    omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      clear hsum_nat0 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase310b hcase320a hcase320b hcase300b hcase420b hcase410a hcase410b hcase401a hcase440b hcase430b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase320a hcase320b hcase300a hcase300b hcase420a hcase420b hcase410a hcase410b hcase401a hcase440a hcase440b hcase431a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14
                      omega
                  ·
                    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase320a hcase320b hcase300a hcase300b hcase420b hcase410b hcase401a hcase441a hcase010b hcase430b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase320a hcase320b hcase300a hcase300b hcase420a hcase420b hcase410a hcase410b hcase401a hcase441a hcase441b hcase010a hcase010b hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase320a hcase320b hcase300a hcase300b hcase420a hcase420b hcase410a hcase410b hcase401a hcase401b hcase441a hcase441b hcase011a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase43
                      omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase341a hcase310b hcase320a hcase320b hcase300b hcase420b hcase430b hcase440b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40
                    omega
                  ·
                    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                    ·
                      clear hn4 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase310b hcase320a hcase320b hcase300b hcase420b hcase430b hcase441a hcase010b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase320a hcase320b hcase300a hcase300b hcase420a hcase420b hcase411a hcase411b hcase430a hcase430b hcase441a hcase441b hcase011a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase320a hcase320b hcase300a hcase300b hcase420a hcase420b hcase411a hcase431a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase320b hcase300a hcase300b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase41 hcase43 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase310b hcase320b hcase301a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase130b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase131a hcase131b hcase400b hcase420b hcase010b hcase430b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase41 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase131a hcase131b hcase400b hcase420b hcase010a hcase010b hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase41 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase321a hcase321b hcase131a hcase131b hcase400a hcase400b hcase420a hcase420b hcase011a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase41 hcase43 hcase44
                  omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase321a hcase131a hcase131b hcase400b hcase421a hcase430b hcase440b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase41
                    omega
                  ·
                    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                    ·
                      clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase321a hcase131a hcase131b hcase400b hcase421a hcase430b hcase441a hcase010b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase41
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase321a hcase321b hcase131a hcase131b hcase400a hcase400b hcase421a hcase421b hcase430a hcase430b hcase441a hcase441b hcase011a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase41
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase321a hcase321b hcase131a hcase131b hcase400a hcase400b hcase421a hcase431a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase41 hcase44
                  omega
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase310b hcase321a hcase131a hcase131b hcase300b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase321a hcase321b hcase131a hcase131b hcase401a hcase401b hcase301a hcase301b hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase310b hcase321a hcase401a hcase301a hcase141a hcase430b hcase420b hcase010b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase321a hcase321b hcase131a hcase131b hcase401a hcase401b hcase301a hcase301b hcase141a hcase141b hcase430a hcase430b hcase420a hcase420b hcase011a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase321a hcase321b hcase131a hcase131b hcase401a hcase301a hcase301b hcase141a hcase141b hcase430a hcase430b hcase421a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase310a hcase310b hcase321a hcase321b hcase131a hcase131b hcase401a hcase301a hcase301b hcase141a hcase141b hcase431a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase41 hcase42 hcase44
                    omega
      ·
        rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
        ·
          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase100b hcase110a hcase110b hcase120b hcase130b hcase00 hcase02 hcase03 hcase04 hcase14 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase140b hcase00 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase141a hcase410b hcase420b hcase400b hcase00 hcase02 hcase03 hcase04 hcase30 hcase32 hcase43 hcase44
                          omega
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hcut5 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase100b hcase110a hcase110b hcase120b hcase131a hcase141a hcase410b hcase420b hcase401a hcase430b hcase440b hcase00 hcase02 hcase03 hcase04 hcase30 hcase32
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010b hcase100a hcase100b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase410b hcase420b hcase401a hcase430b hcase441a hcase00 hcase02 hcase03 hcase04 hcase30 hcase32
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase410a hcase410b hcase420a hcase420b hcase401a hcase431a hcase00 hcase02 hcase03 hcase04 hcase30 hcase32 hcase44
                            omega
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase100b hcase110a hcase110b hcase120b hcase131a hcase141a hcase410b hcase421a hcase430b hcase440b hcase320b hcase00 hcase02 hcase03 hcase04 hcase30 hcase40
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase410a hcase410b hcase421a hcase430b hcase440b hcase321a hcase00 hcase02 hcase03 hcase04 hcase30 hcase40
                              omega
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase010b hcase100a hcase100b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase141a hcase410b hcase421a hcase430b hcase441a hcase400b hcase00 hcase02 hcase03 hcase04 hcase30 hcase32
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase410a hcase410b hcase421a hcase430a hcase430b hcase441a hcase441b hcase401a hcase00 hcase02 hcase03 hcase04 hcase30 hcase32
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase410a hcase410b hcase421a hcase431a hcase00 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase44
                          omega
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase341a hcase311a hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase141a hcase411a hcase300b hcase420b hcase430b hcase440b hcase00 hcase02 hcase03 hcase04 hcase32 hcase40
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase311a hcase010b hcase100a hcase100b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase141a hcase411a hcase300b hcase420b hcase430b hcase441a hcase00 hcase02 hcase03 hcase04 hcase32 hcase40
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase411a hcase300a hcase300b hcase420a hcase420b hcase431a hcase00 hcase02 hcase03 hcase04 hcase32 hcase40 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase411a hcase300a hcase300b hcase421a hcase00 hcase02 hcase03 hcase04 hcase32 hcase40 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100b hcase110b hcase120a hcase120b hcase131a hcase141a hcase411a hcase411b hcase00 hcase02 hcase03 hcase04 hcase32 hcase40 hcase42 hcase43 hcase44
                        omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase130a hcase130b hcase140b hcase00 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase010a hcase010b hcase100b hcase110a hcase110b hcase121a hcase130b hcase141a hcase00 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase131a hcase131b hcase320a hcase320b hcase140b hcase00 hcase02 hcase03 hcase04 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              clear hn4 hsum_nat0 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase341a hcase311a hcase010a hcase010b hcase100b hcase110a hcase110b hcase121a hcase131a hcase320a hcase320b hcase141a hcase420b hcase410a hcase410b hcase440b hcase430b hcase00 hcase02 hcase03 hcase04 hcase30 hcase40
                              omega
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase131a hcase131b hcase320a hcase320b hcase141a hcase141b hcase420b hcase410b hcase440b hcase431a hcase400b hcase00 hcase02 hcase03 hcase04 hcase30
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase131a hcase131b hcase320a hcase320b hcase141a hcase141b hcase420a hcase420b hcase410a hcase410b hcase440a hcase440b hcase431a hcase401a hcase00 hcase02 hcase03 hcase04 hcase30
                                omega
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010b hcase100a hcase100b hcase110a hcase110b hcase121b hcase131b hcase320a hcase320b hcase141a hcase141b hcase420b hcase410b hcase441a hcase430b hcase400b hcase00 hcase02 hcase03 hcase04 hcase30
                                omega
                              ·
                                clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase131a hcase131b hcase320a hcase320b hcase141a hcase141b hcase420b hcase410b hcase441a hcase430b hcase401a hcase00 hcase02 hcase03 hcase04 hcase30
                                omega
                            ·
                              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                              ·
                                clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121b hcase131b hcase320a hcase320b hcase141a hcase141b hcase420b hcase410b hcase441a hcase431a hcase400b hcase00 hcase02 hcase03 hcase04 hcase30
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase131a hcase131b hcase320a hcase320b hcase141a hcase141b hcase420a hcase420b hcase410a hcase410b hcase441a hcase441b hcase431a hcase401a hcase00 hcase02 hcase03 hcase04 hcase30
                                omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010b hcase100a hcase100b hcase110a hcase110b hcase121b hcase131a hcase131b hcase320a hcase320b hcase141a hcase141b hcase420b hcase411a hcase400b hcase430b hcase00 hcase02 hcase03 hcase04 hcase30 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase131a hcase131b hcase320a hcase320b hcase141a hcase141b hcase420a hcase420b hcase411a hcase400a hcase400b hcase431a hcase00 hcase02 hcase03 hcase04 hcase30 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase131a hcase131b hcase320a hcase320b hcase141a hcase141b hcase420a hcase420b hcase411a hcase401a hcase00 hcase02 hcase03 hcase04 hcase30 hcase43 hcase44
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase131a hcase131b hcase320b hcase141a hcase141b hcase421a hcase00 hcase02 hcase03 hcase04 hcase30 hcase40 hcase41 hcase43 hcase44
                        omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010b hcase100a hcase100b hcase110a hcase110b hcase121b hcase131b hcase321a hcase321b hcase420b hcase410b hcase430b hcase400b hcase00 hcase02 hcase03 hcase04 hcase14 hcase30 hcase44
                            omega
                          ·
                            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase330a hcase330b hcase311a hcase311b hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase131a hcase131b hcase420b hcase410a hcase410b hcase430b hcase401a hcase140b hcase00 hcase02 hcase03 hcase04 hcase30 hcase44
                              omega
                            ·
                              clear hn4 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase311a hcase010b hcase100b hcase110a hcase110b hcase121a hcase131a hcase321a hcase420b hcase410a hcase410b hcase430b hcase401a hcase141a hcase00 hcase02 hcase03 hcase04 hcase30 hcase44
                              omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121b hcase131b hcase321a hcase321b hcase420b hcase410b hcase431a hcase400b hcase00 hcase02 hcase03 hcase04 hcase14 hcase30 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase131a hcase131b hcase321a hcase321b hcase420a hcase420b hcase410a hcase410b hcase431a hcase401a hcase00 hcase02 hcase03 hcase04 hcase14 hcase30 hcase44
                            omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121b hcase131a hcase131b hcase420b hcase411a hcase400b hcase00 hcase02 hcase03 hcase04 hcase14 hcase30 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase131a hcase131b hcase321a hcase321b hcase420a hcase420b hcase411a hcase401a hcase00 hcase02 hcase03 hcase04 hcase14 hcase30 hcase43 hcase44
                          omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase131a hcase131b hcase321a hcase421a hcase430b hcase440b hcase00 hcase02 hcase03 hcase04 hcase14 hcase30 hcase40 hcase41
                          omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010b hcase100a hcase100b hcase110a hcase110b hcase121b hcase131a hcase131b hcase321a hcase421a hcase430b hcase441a hcase400b hcase00 hcase02 hcase03 hcase04 hcase14 hcase30 hcase41
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase131a hcase131b hcase321a hcase321b hcase421a hcase430a hcase430b hcase441a hcase441b hcase401a hcase00 hcase02 hcase03 hcase04 hcase14 hcase30 hcase41
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase110a hcase110b hcase121a hcase121b hcase131a hcase131b hcase321a hcase321b hcase421a hcase431a hcase00 hcase02 hcase03 hcase04 hcase14 hcase30 hcase40 hcase41 hcase44
                        omega
            ·
              rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase100b hcase111a hcase120b hcase130b hcase00 hcase02 hcase03 hcase04 hcase14 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase111a hcase111b hcase120a hcase120b hcase131a hcase131b hcase140b hcase00 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase100a hcase100b hcase120a hcase120b hcase131a hcase131b hcase141a hcase300a hcase300b hcase320b hcase400b hcase410b hcase00 hcase02 hcase03 hcase04 hcase42 hcase43 hcase44
                            omega
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase311a hcase010a hcase010b hcase100a hcase100b hcase120a hcase120b hcase131a hcase131b hcase141a hcase300b hcase320a hcase320b hcase400a hcase400b hcase411a hcase420b hcase00 hcase02 hcase03 hcase04 hcase43 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase111a hcase111b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase300a hcase300b hcase320a hcase320b hcase400a hcase400b hcase411a hcase421a hcase00 hcase02 hcase03 hcase04 hcase43 hcase44
                              omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase311a hcase010a hcase010b hcase100a hcase100b hcase120a hcase120b hcase131a hcase131b hcase141a hcase300b hcase320a hcase320b hcase401a hcase420b hcase00 hcase02 hcase03 hcase04 hcase41 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase111a hcase111b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase300a hcase300b hcase320a hcase320b hcase401a hcase421a hcase00 hcase02 hcase03 hcase04 hcase41 hcase43 hcase44
                            omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase311a hcase010a hcase010b hcase100a hcase100b hcase120a hcase120b hcase131a hcase131b hcase141a hcase300b hcase321a hcase400a hcase400b hcase420b hcase00 hcase02 hcase03 hcase04 hcase41 hcase43 hcase44
                            omega
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase100a hcase100b hcase120a hcase120b hcase131a hcase131b hcase141a hcase300a hcase300b hcase321a hcase400b hcase421a hcase410b hcase00 hcase02 hcase03 hcase04 hcase43 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase111a hcase111b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase300a hcase300b hcase321a hcase321b hcase400a hcase400b hcase421a hcase411a hcase00 hcase02 hcase03 hcase04 hcase43 hcase44
                              omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase311a hcase010a hcase010b hcase100a hcase100b hcase120a hcase120b hcase131a hcase131b hcase141a hcase300b hcase321a hcase401a hcase420b hcase00 hcase02 hcase03 hcase04 hcase41 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase111a hcase111b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase300a hcase300b hcase321a hcase321b hcase401a hcase421a hcase00 hcase02 hcase03 hcase04 hcase41 hcase43 hcase44
                            omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase010b hcase100a hcase100b hcase120a hcase120b hcase131a hcase131b hcase141a hcase301a hcase301b hcase410b hcase430b hcase420b hcase400b hcase00 hcase02 hcase03 hcase04 hcase32 hcase44
                              omega
                            ·
                              clear hn4 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase311a hcase010b hcase100b hcase111a hcase120a hcase120b hcase131a hcase141a hcase301a hcase410a hcase410b hcase430b hcase420b hcase401a hcase00 hcase02 hcase03 hcase04 hcase32 hcase44
                              omega
                          ·
                            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase010b hcase100a hcase100b hcase120a hcase120b hcase131a hcase131b hcase141a hcase301a hcase301b hcase410b hcase430b hcase421a hcase400b hcase00 hcase02 hcase03 hcase04 hcase32 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase111a hcase111b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase301a hcase301b hcase410a hcase410b hcase430a hcase430b hcase421a hcase401a hcase00 hcase02 hcase03 hcase04 hcase32 hcase44
                              omega
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase100a hcase100b hcase120a hcase120b hcase131a hcase131b hcase141a hcase301a hcase301b hcase410b hcase431a hcase400b hcase00 hcase02 hcase03 hcase04 hcase32 hcase42 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase111a hcase111b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase301a hcase301b hcase410a hcase410b hcase431a hcase401a hcase00 hcase02 hcase03 hcase04 hcase32 hcase42 hcase44
                            omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010b hcase100a hcase100b hcase111b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase301a hcase301b hcase411a hcase400b hcase420b hcase430b hcase00 hcase02 hcase03 hcase04 hcase32 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase111a hcase111b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase301a hcase301b hcase411a hcase400a hcase400b hcase420a hcase420b hcase431a hcase00 hcase02 hcase03 hcase04 hcase32 hcase44
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase111a hcase111b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase301a hcase301b hcase411a hcase400a hcase400b hcase421a hcase00 hcase02 hcase03 hcase04 hcase32 hcase43 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase111a hcase111b hcase120a hcase120b hcase131a hcase131b hcase141a hcase141b hcase301a hcase301b hcase411a hcase401a hcase00 hcase02 hcase03 hcase04 hcase32 hcase42 hcase43 hcase44
                          omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase111a hcase111b hcase121a hcase121b hcase140b hcase00 hcase02 hcase03 hcase04 hcase13 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase010a hcase010b hcase100b hcase111a hcase121a hcase141a hcase130b hcase00 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase100a hcase100b hcase111a hcase121a hcase141a hcase131a hcase00 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
          ·
            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase420b hcase400b hcase410b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase32 hcase43 hcase44
                  omega
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010b hcase101b hcase420b hcase400b hcase411a hcase430b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase32 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase101a hcase101b hcase420a hcase420b hcase400a hcase400b hcase411a hcase431a hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase32 hcase44
                    omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase101a hcase420a hcase420b hcase401a hcase401b hcase130b hcase120b hcase00 hcase02 hcase03 hcase04 hcase11 hcase14 hcase30 hcase32 hcase41 hcase43 hcase44
                    omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase101a hcase101b hcase420a hcase420b hcase401a hcase401b hcase130a hcase130b hcase121a hcase121b hcase140b hcase00 hcase02 hcase03 hcase04 hcase11 hcase30 hcase32 hcase41 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase010a hcase010b hcase101a hcase420a hcase420b hcase401a hcase401b hcase130b hcase121a hcase141a hcase00 hcase02 hcase03 hcase04 hcase11 hcase30 hcase32 hcase41 hcase43 hcase44
                      omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut5 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase101a hcase101b hcase420b hcase401a hcase410b hcase430b hcase440b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase14 hcase30 hcase32
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010b hcase101a hcase101b hcase420b hcase401a hcase131a hcase131b hcase410b hcase430b hcase441a hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase14 hcase30 hcase32
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase101a hcase101b hcase420a hcase420b hcase401a hcase131a hcase131b hcase410a hcase410b hcase431a hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase14 hcase30 hcase32 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase101a hcase101b hcase420a hcase420b hcase401a hcase131a hcase131b hcase411a hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase14 hcase30 hcase32 hcase43 hcase44
                    omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase101a hcase101b hcase320b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase40 hcase41 hcase43 hcase44
                omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase041a hcase330a hcase330b hcase341a hcase341b hcase010b hcase421a hcase321a hcase410b hcase430b hcase400b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase101a hcase101b hcase421a hcase321a hcase321b hcase410a hcase410b hcase430a hcase430b hcase401a hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase101a hcase101b hcase421a hcase321a hcase321b hcase410a hcase410b hcase431a hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase40 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase010a hcase010b hcase101a hcase101b hcase421a hcase321a hcase321b hcase411a hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase40 hcase43 hcase44
                  omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase330a hcase330b hcase341a hcase341b hcase311a hcase311b hcase011a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
  ·
    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
    ·
      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
      ·
        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase340b hcase400a hcase400b hcase300b hcase410a hcase410b hcase310b hcase430a hcase430b hcase420a hcase420b hcase320b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase44
                      omega
                    ·
                      clear hn4 hcut5 hcut15 hcut36 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase010b hcase340b hcase400b hcase300b hcase410a hcase410b hcase310b hcase430b hcase420b hcase321a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase44
                      omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331b hcase010a hcase010b hcase340a hcase340b hcase400b hcase300a hcase300b hcase410b hcase310a hcase310b hcase430b hcase421a hcase440b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase32
                      omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase340b hcase400a hcase400b hcase300b hcase410a hcase410b hcase310b hcase430a hcase430b hcase421a hcase421b hcase441a hcase441b hcase320b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase331b hcase010b hcase340a hcase340b hcase400b hcase300a hcase300b hcase410a hcase410b hcase310a hcase310b hcase430b hcase421a hcase441a hcase321a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14
                        omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase340b hcase400a hcase400b hcase300b hcase410a hcase410b hcase310b hcase431a hcase431b hcase320b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase42 hcase44
                    omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400b hcase300a hcase300b hcase410b hcase310a hcase310b hcase431a hcase321a hcase321b hcase440b hcase420b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase300a hcase300b hcase410a hcase410b hcase310a hcase310b hcase431a hcase321a hcase321b hcase440a hcase440b hcase421a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14
                        omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hcut5 hcut15 hcut36 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase010a hcase010b hcase340b hcase400b hcase300b hcase410a hcase410b hcase310b hcase431a hcase321a hcase441a hcase420b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase300a hcase300b hcase410a hcase410b hcase310a hcase310b hcase431a hcase321a hcase321b hcase441a hcase441b hcase421a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14
                        omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase300a hcase300b hcase410a hcase410b hcase311a hcase311b hcase140b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase32 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400b hcase300a hcase300b hcase410b hcase141a hcase420b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase32 hcase43 hcase44
                    omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase331b hcase010b hcase340a hcase340b hcase400b hcase300a hcase300b hcase410b hcase141a hcase421a hcase430b hcase320b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase331b hcase010b hcase340a hcase340b hcase400b hcase300a hcase300b hcase410b hcase141a hcase421a hcase430b hcase321a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase300a hcase300b hcase410a hcase410b hcase311a hcase311b hcase141a hcase141b hcase421a hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase32 hcase44
                      omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400b hcase300a hcase300b hcase411a hcase420b hcase440b hcase430b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase300a hcase300b hcase411a hcase420a hcase420b hcase440a hcase440b hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32
                    omega
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase331b hcase010b hcase340a hcase340b hcase400b hcase300a hcase300b hcase411a hcase420b hcase441a hcase430b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase300a hcase300b hcase411a hcase420a hcase420b hcase441a hcase441b hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase300a hcase300b hcase411a hcase421a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase43 hcase44
                omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase301b hcase130a hcase130b hcase320a hcase320b hcase140b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase130b hcase320b hcase141a hcase120b hcase100b hcase00 hcase02 hcase03 hcase04 hcase11 hcase31 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase130b hcase320b hcase141a hcase120b hcase101a hcase00 hcase02 hcase03 hcase04 hcase11 hcase31 hcase41 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase130a hcase130b hcase320b hcase141a hcase141b hcase121a hcase121b hcase310b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase301b hcase130b hcase320a hcase320b hcase141a hcase121a hcase311a hcase100b hcase00 hcase02 hcase03 hcase04 hcase11 hcase41 hcase42 hcase43 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase301b hcase130b hcase320a hcase320b hcase141a hcase121a hcase311a hcase101a hcase00 hcase02 hcase03 hcase04 hcase11 hcase41 hcase42 hcase43 hcase44
                        omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase301b hcase130b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase31 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase301b hcase131a hcase131b hcase420a hcase420b hcase320a hcase320b hcase100a hcase100b hcase140b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase31 hcase41 hcase43 hcase44
                      omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase131a hcase420a hcase420b hcase320a hcase320b hcase100b hcase141a hcase110b hcase00 hcase02 hcase03 hcase04 hcase12 hcase31 hcase41 hcase43 hcase44
                        omega
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase131a hcase131b hcase420a hcase420b hcase320b hcase100a hcase100b hcase141a hcase141b hcase111a hcase111b hcase310b hcase00 hcase02 hcase03 hcase04 hcase12 hcase41 hcase43 hcase44
                          omega
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase010a hcase010b hcase340a hcase340b hcase400b hcase301a hcase131a hcase131b hcase420b hcase320b hcase100a hcase100b hcase141a hcase311a hcase410b hcase00 hcase02 hcase03 hcase04 hcase12 hcase43 hcase44
                            omega
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase331b hcase010b hcase340a hcase340b hcase400b hcase301a hcase301b hcase131a hcase131b hcase420b hcase320a hcase320b hcase100a hcase100b hcase141a hcase141b hcase111b hcase311a hcase311b hcase411a hcase430b hcase00 hcase02 hcase03 hcase04 hcase12 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase301b hcase131a hcase131b hcase420a hcase420b hcase320a hcase320b hcase100a hcase100b hcase141a hcase141b hcase111a hcase111b hcase311a hcase311b hcase411a hcase431a hcase00 hcase02 hcase03 hcase04 hcase12 hcase44
                              omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400b hcase301a hcase301b hcase131b hcase420b hcase320a hcase320b hcase101b hcase410b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase14 hcase31 hcase43 hcase44
                      omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase331b hcase010b hcase340a hcase340b hcase400b hcase301a hcase301b hcase131a hcase131b hcase420b hcase320a hcase320b hcase101b hcase411a hcase430b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase14 hcase31 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase301b hcase131a hcase131b hcase420a hcase420b hcase320a hcase320b hcase101a hcase101b hcase411a hcase431a hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase14 hcase31 hcase44
                        omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase301b hcase131a hcase131b hcase420a hcase420b hcase321a hcase321b hcase140b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase41 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400b hcase131a hcase420b hcase141a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase41 hcase43 hcase44
                    omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase301b hcase131a hcase131b hcase421a hcase421b hcase430a hcase430b hcase140b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase41 hcase44
                    omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase301b hcase131a hcase131b hcase430a hcase430b hcase141a hcase141b hcase320b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase41 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase331b hcase010b hcase340a hcase340b hcase400b hcase131a hcase421a hcase430b hcase141a hcase321a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase41 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase400a hcase400b hcase301a hcase301b hcase131a hcase131b hcase421a hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase31 hcase32 hcase41 hcase44
                  omega
        ·
          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
          ·
            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
            ·
              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase010a hcase010b hcase340a hcase340b hcase401a hcase410a hcase410b hcase420b hcase440b hcase430b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase401a hcase410a hcase410b hcase420a hcase420b hcase440a hcase440b hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32
                  omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase331a hcase331b hcase010b hcase340a hcase340b hcase401a hcase410b hcase420b hcase441a hcase430b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase401a hcase410a hcase410b hcase420a hcase420b hcase441a hcase441b hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase401a hcase410a hcase410b hcase421a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase43 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase340a hcase340b hcase401a hcase411a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase42 hcase43 hcase44
            omega
      ·
        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
        ·
          rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase130b hcase120b hcase100b hcase110b hcase140b hcase00 hcase02 hcase03 hcase04 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase341a hcase130b hcase120b hcase100b hcase110a hcase110b hcase141a hcase320b hcase00 hcase02 hcase03 hcase04 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut43 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase341a hcase130b hcase120b hcase100b hcase110a hcase110b hcase141a hcase321a hcase00 hcase02 hcase03 hcase04 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase130b hcase120b hcase100b hcase111a hcase140b hcase00 hcase02 hcase03 hcase04 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase130b hcase120b hcase100b hcase111a hcase141a hcase00 hcase02 hcase03 hcase04 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase130a hcase130b hcase120a hcase120b hcase101a hcase101b hcase140b hcase00 hcase02 hcase03 hcase04 hcase11 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase341a hcase130b hcase120b hcase101a hcase141a hcase320b hcase00 hcase02 hcase03 hcase04 hcase11 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase341a hcase130b hcase120b hcase101a hcase141a hcase321a hcase00 hcase02 hcase03 hcase04 hcase11 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase130a hcase130b hcase310b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase14 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331b hcase010a hcase010b hcase341b hcase130b hcase121a hcase311a hcase311b hcase100b hcase110b hcase140b hcase00 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase130b hcase121a hcase311a hcase100b hcase110a hcase110b hcase141a hcase00 hcase02 hcase03 hcase04 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase130b hcase121a hcase311a hcase100b hcase111a hcase00 hcase02 hcase03 hcase04 hcase14 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase130a hcase130b hcase121a hcase121b hcase311a hcase311b hcase101a hcase101b hcase140b hcase00 hcase02 hcase03 hcase04 hcase11 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut11 hcut4 hcut9 hcut33 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase130b hcase121a hcase311a hcase101a hcase141a hcase00 hcase02 hcase03 hcase04 hcase11 hcase30 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase341a hcase131a hcase131b hcase300a hcase300b hcase410a hcase410b hcase400a hcase400b hcase310b hcase320b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase331a hcase331b hcase010b hcase341a hcase341b hcase131b hcase300a hcase300b hcase410b hcase400b hcase310a hcase310b hcase321a hcase321b hcase420b hcase430b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase131b hcase300a hcase300b hcase410b hcase400b hcase310a hcase310b hcase321a hcase321b hcase420b hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase44
                        omega
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331b hcase010a hcase010b hcase341b hcase131a hcase131b hcase300a hcase300b hcase410b hcase400b hcase310a hcase310b hcase321a hcase321b hcase421a hcase440b hcase430b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase131a hcase131b hcase300a hcase300b hcase410a hcase410b hcase400a hcase400b hcase310a hcase310b hcase321a hcase321b hcase421a hcase440a hcase440b hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14
                          omega
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          clear hn4 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase331b hcase010b hcase341a hcase341b hcase131a hcase131b hcase300a hcase300b hcase410a hcase410b hcase400b hcase310a hcase310b hcase321a hcase421a hcase441a hcase430b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase131a hcase131b hcase300a hcase300b hcase410a hcase410b hcase400a hcase400b hcase310a hcase310b hcase321a hcase321b hcase421a hcase441a hcase441b hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14
                          omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase131a hcase131b hcase300a hcase300b hcase410a hcase410b hcase400a hcase400b hcase311a hcase311b hcase140b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase32 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase131a hcase131b hcase300a hcase300b hcase410b hcase400b hcase141a hcase420b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase32 hcase43 hcase44
                      omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut15 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase331b hcase010b hcase341a hcase341b hcase131a hcase131b hcase300a hcase300b hcase410b hcase400b hcase141a hcase421a hcase430b hcase320b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase341a hcase131a hcase131b hcase300a hcase300b hcase410a hcase410b hcase400a hcase400b hcase311a hcase141a hcase141b hcase421a hcase421b hcase430a hcase430b hcase321a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase131a hcase131b hcase300a hcase300b hcase410a hcase410b hcase400a hcase400b hcase311a hcase311b hcase141a hcase141b hcase421a hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase32 hcase44
                        omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030b hcase001a hcase041a hcase010b hcase131a hcase131b hcase300a hcase300b hcase410a hcase410b hcase401a hcase420b hcase430b hcase140b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase44
                      omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase341a hcase131a hcase131b hcase300b hcase410a hcase410b hcase420a hcase420b hcase430a hcase430b hcase141a hcase141b hcase310b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase32 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase010b hcase341a hcase131a hcase131b hcase300b hcase410a hcase410b hcase401a hcase420b hcase430b hcase141a hcase311a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase32 hcase44
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase131a hcase131b hcase300a hcase300b hcase410a hcase410b hcase401a hcase420a hcase420b hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase31 hcase32 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase131a hcase131b hcase300a hcase300b hcase410a hcase410b hcase401a hcase421a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase31 hcase32 hcase43 hcase44
                  omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase131a hcase131b hcase300a hcase300b hcase411a hcase411b hcase140b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase31 hcase32 hcase40 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase341a hcase131a hcase131b hcase300b hcase141a hcase141b hcase310b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase32 hcase40 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hcut5 hcut15 hcut36 hcut28 hcut23 hcut12 hcut32 hcut43 hcut3 hcut18 hcut11 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020b hcase030a hcase030b hcase001a hcase041a hcase331a hcase010b hcase341a hcase131a hcase131b hcase300b hcase411a hcase141a hcase311a hcase430b hcase420b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase32 hcase40 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase131a hcase131b hcase300a hcase300b hcase411a hcase141a hcase141b hcase311a hcase311b hcase430a hcase430b hcase421a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase32 hcase40 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase331b hcase010a hcase010b hcase341a hcase341b hcase131a hcase131b hcase300a hcase300b hcase411a hcase141a hcase141b hcase311a hcase311b hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase32 hcase40 hcase42 hcase44
                    omega
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase341a hcase131a hcase131b hcase301a hcase310b hcase320b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase341a hcase131a hcase131b hcase301a hcase310a hcase310b hcase321a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase041b hcase331a hcase010a hcase010b hcase341a hcase131a hcase131b hcase301a hcase311a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase14 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut5 hcut15 hcut36 hcut28 hcut2 hcut23 hcut12 hcut26 hcut32 hcut43 hcut3 hcut18 hcut11 hcut4 hcut9 hcut33 hcut35 hcut29 hcut38 hcut46 hcut45 hcut16 hcut1 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase020a hcase020b hcase030a hcase030b hcase001a hcase001b hcase041a hcase331a hcase331b hcase011a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega

#print axioms symbolic_v2_mask551_integer_shard003
end Jsp404.SixExactFloorKernel
