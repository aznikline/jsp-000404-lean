import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask200_integer_shard006 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut2 : (s02 + s03 + s13 + s30 + s31 + s41 + s42 + u02 + u03 + u13 + u30 + u31 + u41 + u42) + 1 ≤ (n))
    (hcut7 : (s00 + s04 + s11 + s33 + s40 + s44 + u00 + u04 + u11 + u33 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut34 : (s13 + u13 + 3) + 1 ≤ (n))
    (hcut26 : (s01 + s32 + u01 + u32) + 1 ≤ (s11 + 2))
    (hcut74 : (s00 + s01 + s04 + s13 + s14 + s40 + u00 + u01 + u04 + u13 + u14 + u40) + 1 ≤ (2 * n + 1))
    (hcut46 : (s00 + s04 + s32 + s40 + u00 + u04 + u32 + u40) + 1 ≤ (2 * n + 1))
    (hcut59 : (s00 + s11 + s44 + u00 + u11 + u44) + 1 ≤ (n + 1))
    (hcut49 : (s11 + s33 + s44 + u11 + u33 + u44) + 1 ≤ (n + 1))
    (hcut57 : (s03 + s31 + u03 + u31 + 2) + 1 ≤ (n))
    (hcut21 : (s40 + s43 + u40 + u43) + 1 ≤ (n))
    (hcut44 : (s14 + s41 + u14 + u41 + 2) + 1 ≤ (n))
    (hcut73 : (s14 + s40 + u14 + u40) + 1 ≤ (n))
    (hcut27 : (s34 + u34) + 1 ≤ (s44 + 2))
    (hcut77 : (s03 + s04 + s10 + u03 + u04 + u10) + 1 ≤ (n + 1))
    (hcut20 : (s00 + s04 + s33 + s40 + u00 + u04 + u33 + u40) + 1 ≤ (2 * n))
    (hcut63 : (s41 + s42 + s44 + u41 + u42 + u44) + 1 ≤ (n))
    (hcut51 : (s02 + s13 + s14 + s30 + u02 + u13 + u14 + u30) + 1 ≤ (n))
    (hcut10 : (s10 + s13 + s14 + s42 + u10 + u13 + u14 + u42) + 1 ≤ (n))
    (hcut71 : (s13 + s14 + s30 + s41 + u13 + u14 + u30 + u41) + 1 ≤ (n))
    (hcut6 : (s04 + s40 + u04 + u40) + 1 ≤ (n + 2))
    (hcut33 : (s30 + s31 + u30 + u31 + 2) + 1 ≤ (n))
    (hcut56 : (s03 + s30 + u03 + u30 + 2) + 1 ≤ (n))
    (hcut3 : (s10 + u10) + 1 ≤ (s00 + 2))
    (hcut0 : (s12 + s43 + u12 + u43) + 1 ≤ (s33 + 2))
    (hcut70 : (s13 + s14 + s31 + s41 + u13 + u14 + u31 + u41) + 1 ≤ (n))
    (hcut58 : (s00 + s11 + s33 + u00 + u11 + u33) + 1 ≤ (n + 1))
    (hcut25 : (s11 + s33 + u11 + u33) + 1 ≤ (n))
    (hcut69 : (s41 + s42 + s43 + s44 + u41 + u42 + u43 + u44) + 1 ≤ (n + 1))
    (hcut78 : (s00 + s03 + s13 + s14 + u00 + u03 + u13 + u14) + 1 ≤ (n + 2))
    (hcut54 : (s01 + s03 + s04 + u01 + u03 + u04) + 1 ≤ (n))
    (hcut68 : (s40 + s41 + s42 + s43 + u40 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut22 : (s42 + u42 + 3) + 1 ≤ (n))
    (hcut47 : (s02 + s13 + s14 + s31 + u02 + u13 + u14 + u31 + 1) + 1 ≤ (n))
    (hcut9 : (s40 + s42 + s43 + s44 + u40 + u42 + u43 + u44) + 1 ≤ (n + 1))
    (hcut19 : (s02 + s03 + u02 + u03 + 2) + 1 ≤ (n))
    (hcut40 : (s40 + s41 + s42 + u40 + u41 + u42) + 1 ≤ (n))
    (hcut37 : (s00 + s33 + s44 + u00 + u33 + u44) + 1 ≤ (n + 1))
    (hcut42 : (s04 + s12 + s40 + s44 + u04 + u12 + u40 + u44) + 1 ≤ (2 * n))
    (hcut1 : (n) + 1 ≤ (s04 + s40 + 4))
    (hcut67 : (s02 + s03 + s04 + u02 + u03 + u04) + 1 ≤ (n))
    (hcut35 : (s00 + s04 + s40 + s44 + u00 + u04 + u40 + u44) + 1 ≤ (2 * n))
    (hcut52 : (s00 + s01 + s02 + u00 + u01 + u02 + 1) + 1 ≤ (n))
    (hcut4 : (s02 + s03 + s30 + s31 + s34 + s41 + s42 + s43 + u02 + u03 + u30 + u31 + u34 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut30 : (s04 + s11 + s40 + s44 + u04 + u11 + u40 + u44) + 1 ≤ (2 * n))
    (hcut45 : (s02 + s13 + s14 + u02 + u13 + u14 + 1) + 1 ≤ (n))
    (hcut53 : (s13 + s14 + s41 + u13 + u14 + u41 + 1) + 1 ≤ (n))
    (hcut43 : (s11 + s34 + u11 + u34) + 1 ≤ (n))
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
    (hcase031a : 1 ≤ s03)
    (hcase031b : u03 = 1)
    : False := by
  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
  ·
    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
    ·
      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
      ·
        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
        ·
          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase020a hcase020b hcase040a hcase040b hcase320b hcase340b hcase300b hcase330b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase031a hcase040b hcase320a hcase320b hcase340a hcase340b hcase300a hcase300b hcase331a hcase331b hcase000b hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase031a hcase040b hcase320b hcase340b hcase300b hcase331a hcase001a hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
          ·
            clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase031a hcase040b hcase320a hcase320b hcase340a hcase340b hcase000b hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase031a hcase040b hcase320b hcase340b hcase301a hcase001a hcase310b hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase020a hcase020b hcase040a hcase040b hcase320b hcase340b hcase301a hcase001a hcase001b hcase311a hcase330b hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020a hcase020b hcase031a hcase040b hcase320b hcase340b hcase301a hcase001a hcase311a hcase331a hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
      ·
        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
        ·
          rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
          ·
            clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase031a hcase040b hcase320a hcase320b hcase341a hcase341b hcase310a hcase310b hcase000b hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase020a hcase020b hcase040b hcase320b hcase341a hcase310b hcase001a hcase001b hcase330b hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase031a hcase040b hcase320b hcase341a hcase310b hcase001a hcase331a hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
          ·
            rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase031a hcase040b hcase320a hcase320b hcase341a hcase341b hcase300a hcase300b hcase000b hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut21 hcut44 hcut73 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase031a hcase040b hcase320b hcase341a hcase311a hcase300b hcase001a hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020a hcase020b hcase031a hcase040b hcase320a hcase320b hcase000b hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut42 hcut1 hcut67 hcut35 hcut52 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020a hcase020b hcase031a hcase040b hcase320b hcase311a hcase301a hcase001a hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
    ·
      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase110b hcase00 hcase01 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
      ·
        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
        ·
          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010b hcase020b hcase031a hcase040b hcase321a hcase321b hcase111a hcase111b hcase000b hcase01 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat4 hcut2 hcut7 hcut34 hcut74 hcut46 hcut59 hcut49 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase020b hcase031a hcase040b hcase321a hcase111a hcase001a hcase340b hcase300b hcase01 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut2 hcut7 hcut34 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut3 hcut0 hcut70 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase020b hcase031a hcase040b hcase321a hcase111a hcase001a hcase340b hcase301a hcase310b hcase01 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut7 hcut34 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase020a hcase020b hcase031a hcase040b hcase321a hcase111a hcase001a hcase340b hcase301a hcase311a hcase01 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut2 hcut7 hcut34 hcut74 hcut46 hcut49 hcut57 hcut21 hcut44 hcut73 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase020b hcase031a hcase040b hcase321a hcase111a hcase001a hcase341a hcase310b hcase330b hcase01 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hcut2 hcut7 hcut34 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut3 hcut0 hcut70 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase020b hcase031a hcase040b hcase321a hcase111a hcase001a hcase341a hcase310b hcase331a hcase01 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase30 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                clear hn4 hsum_nat1 hcut2 hcut7 hcut34 hcut74 hcut46 hcut59 hcut49 hcut21 hcut44 hcut73 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase020b hcase031a hcase040b hcase321a hcase111a hcase001a hcase341a hcase311a hcase300b hcase01 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase010a hcase010b hcase020a hcase020b hcase031a hcase031b hcase040a hcase040b hcase321a hcase111a hcase111b hcase001a hcase001b hcase341a hcase311a hcase301a hcase01 hcase02 hcase03 hcase10 hcase12 hcase13 hcase14 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
  ·
    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut2 hcut7 hcut34 hcut26 hcut74 hcut46 hcut59 hcut49 hcut57 hcut21 hcut44 hcut73 hcut27 hcut77 hcut20 hcut63 hcut51 hcut10 hcut71 hcut6 hcut33 hcut56 hcut3 hcut0 hcut70 hcut58 hcut25 hcut69 hcut78 hcut54 hcut68 hcut22 hcut47 hcut9 hcut19 hcut40 hcut37 hcut42 hcut1 hcut67 hcut35 hcut52 hcut4 hcut30 hcut45 hcut53 hcut43 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase010a hcase010b hcase020a hcase020b hcase031a hcase041a hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
    omega

#print axioms symbolic_v2_mask200_integer_shard006
end Jsp404.SixExactFloorKernel
