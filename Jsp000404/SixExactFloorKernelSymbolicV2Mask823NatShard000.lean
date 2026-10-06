import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask823_integer_shard000 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut30 : (s33 + s34 + s43 + u33 + u34 + u43) + 1 ≤ (n))
    (hcut92 : (s01 + s10 + s11 + s34 + s42 + s43 + u01 + u10 + u11 + u34 + u42 + u43) + 1 ≤ (n + 1))
    (hcut9 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 2))
    (hcut2 : (s12 + s41 + u12 + u41) + 1 ≤ (s31 + 2))
    (hcut82 : (s02 + s30 + s41 + s42 + u02 + u30 + u41 + u42 + 1) + 1 ≤ (n))
    (hcut10 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut0 : (s02 + s03 + s10 + s11 + s14 + s42 + s43 + u02 + u03 + u10 + u11 + u14 + u42 + u43) + 1 ≤ (n + 1))
    (hcut98 : (s00 + s01 + s04 + s13 + s31 + s34 + u00 + u01 + u04 + u13 + u31 + u34) + 1 ≤ (2 * n))
    (hcut11 : (s01 + s30 + s41 + u01 + u30 + u41 + 1) + 1 ≤ (n))
    (hcut83 : (s30 + s34 + s41 + s42 + u30 + u34 + u41 + u42 + 1) + 1 ≤ (n))
    (hcut4 : (s13 + s31 + u13 + u31 + 1) + 1 ≤ (n))
    (hcut31 : (s13 + s30 + u13 + u30) + 1 ≤ (n))
    (hcut65 : (s10 + s11 + s30 + u10 + u11 + u30 + 4) + 1 ≤ (2 * n))
    (hcut54 : (s13 + s14 + s30 + s31 + u13 + u14 + u30 + u31) + 1 ≤ (n + 1))
    (hcut62 : (s01 + s02 + s33 + s34 + u01 + u02 + u33 + u34) + 1 ≤ (s44 + 2))
    (hcut56 : (s01 + s30 + s41 + s42 + s43 + u01 + u30 + u41 + u42 + u43) + 1 ≤ (n))
    (hcut60 : (s02 + s34 + s40 + s42 + u02 + u34 + u40 + u42) + 1 ≤ (n))
    (hcut24 : (s42 + s43 + s44 + u42 + u43 + u44) + 1 ≤ (n + 1))
    (hcut52 : (s01 + s42 + u01 + u42 + 2) + 1 ≤ (n))
    (hcut45 : (s01 + s02 + s14 + s43 + u01 + u02 + u14 + u43 + 1) + 1 ≤ (n))
    (hcut61 : (s40 + u40) + 1 ≤ (s30 + 2))
    (hcut77 : (s33 + s41 + u33 + u41 + 2) + 1 ≤ (n))
    (hcut97 : (s33 + s34 + s41 + s42 + u33 + u34 + u41 + u42 + 1) + 1 ≤ (n))
    (hcut18 : (s02 + u02 + 3) + 1 ≤ (n))
    (hcut95 : (s33 + s34 + s40 + s42 + u33 + u34 + u40 + u42) + 1 ≤ (n))
    (hcut20 : (s01 + s43 + u01 + u43 + 2) + 1 ≤ (n))
    (hcut50 : (s01 + s30 + s34 + u01 + u30 + u34) + 1 ≤ (n))
    (hcut28 : (s03 + s32 + u03 + u32) + 1 ≤ (s13 + 2))
    (hcut33 : (s34 + s42 + u34 + u42 + 2) + 1 ≤ (n))
    (hcut80 : (s33 + s41 + s42 + u33 + u41 + u42 + 1) + 1 ≤ (n))
    (hcut51 : (s01 + s02 + s33 + u01 + u02 + u33) + 1 ≤ (s44 + 1))
    (hcut48 : (s00 + s01 + s33 + u00 + u01 + u33) + 1 ≤ (n + 1))
    (hcut55 : (s01 + s30 + s41 + s42 + u01 + u30 + u41 + u42) + 1 ≤ (n))
    (hcut87 : (s40 + s41 + s43 + s44 + u40 + u41 + u43 + u44) + 1 ≤ (n + 1))
    (hcut47 : (s41 + s43 + s44 + u41 + u43 + u44) + 1 ≤ (n + 1))
    (hcut43 : (s01 + s02 + s34 + s41 + u01 + u02 + u34 + u41) + 1 ≤ (n))
    (hcut13 : (s01 + s02 + s10 + u01 + u02 + u10 + 1) + 1 ≤ (n))
    (hcut27 : (s02 + s33 + s43 + u02 + u33 + u43 + 1) + 1 ≤ (n))
    (hcut75 : (s00 + s04 + s31 + s44 + u00 + u04 + u31 + u44) + 1 ≤ (2 * n + 1))
    (hcut71 : (s14 + s30 + u14 + u30 + 1) + 1 ≤ (n))
    (hcut88 : (s30 + s33 + s42 + u30 + u33 + u42 + 1) + 1 ≤ (n))
    (hcut35 : (s02 + s33 + s34 + s42 + u02 + u33 + u34 + u42 + 1) + 1 ≤ (n))
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
        clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut30 hcut92 hcut9 hcut2 hcut82 hcut10 hcut0 hcut98 hcut11 hcut83 hcut4 hcut31 hcut65 hcut54 hcut62 hcut56 hcut60 hcut24 hcut52 hcut45 hcut61 hcut77 hcut97 hcut95 hcut20 hcut50 hcut28 hcut33 hcut80 hcut51 hcut48 hcut55 hcut87 hcut47 hcut43 hcut13 hcut27 hcut75 hcut71 hcut88 hcut35 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase030b hcase040b hcase010b hcase00 hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
      ·
        clear hn4 hsum_nat1 hsum_nat3 hcut30 hcut92 hcut9 hcut2 hcut82 hcut10 hcut0 hcut98 hcut11 hcut83 hcut4 hcut31 hcut65 hcut54 hcut62 hcut56 hcut60 hcut24 hcut52 hcut45 hcut61 hcut77 hcut97 hcut18 hcut95 hcut20 hcut50 hcut28 hcut33 hcut80 hcut48 hcut55 hcut87 hcut47 hcut43 hcut13 hcut27 hcut75 hcut71 hcut88 hcut35 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase030b hcase040b hcase011a hcase00 hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
    ·
      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
      ·
        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
        ·
          clear hn4 hsum_nat3 hsum_nat4 hcut30 hcut92 hcut9 hcut2 hcut82 hcut0 hcut98 hcut11 hcut83 hcut4 hcut31 hcut65 hcut54 hcut62 hcut56 hcut60 hcut24 hcut52 hcut45 hcut61 hcut77 hcut97 hcut18 hcut95 hcut20 hcut50 hcut28 hcut33 hcut80 hcut51 hcut48 hcut55 hcut87 hcut47 hcut43 hcut13 hcut27 hcut75 hcut71 hcut88 hcut35 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase030b hcase041a hcase010b hcase020b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut30 hcut92 hcut9 hcut2 hcut82 hcut10 hcut0 hcut98 hcut11 hcut83 hcut4 hcut31 hcut65 hcut54 hcut62 hcut56 hcut60 hcut24 hcut52 hcut45 hcut61 hcut77 hcut97 hcut18 hcut95 hcut20 hcut50 hcut28 hcut33 hcut80 hcut51 hcut48 hcut55 hcut87 hcut47 hcut43 hcut13 hcut27 hcut75 hcut71 hcut88 hcut35 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase030a hcase030b hcase041a hcase010a hcase010b hcase021a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut30 hcut92 hcut9 hcut2 hcut82 hcut10 hcut0 hcut98 hcut11 hcut83 hcut4 hcut31 hcut65 hcut54 hcut62 hcut56 hcut60 hcut24 hcut52 hcut45 hcut61 hcut77 hcut97 hcut18 hcut95 hcut20 hcut50 hcut28 hcut33 hcut80 hcut51 hcut48 hcut55 hcut87 hcut47 hcut43 hcut13 hcut27 hcut75 hcut71 hcut88 hcut35 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase030a hcase030b hcase041a hcase011a hcase00 hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
  ·
    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
    ·
      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
      ·
        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
        ·
          clear hn4 hsum_nat3 hsum_nat4 hcut30 hcut92 hcut9 hcut2 hcut82 hcut10 hcut0 hcut98 hcut11 hcut83 hcut4 hcut31 hcut65 hcut54 hcut62 hcut56 hcut60 hcut24 hcut52 hcut45 hcut61 hcut77 hcut97 hcut18 hcut95 hcut20 hcut50 hcut33 hcut80 hcut51 hcut48 hcut55 hcut87 hcut47 hcut43 hcut13 hcut27 hcut75 hcut71 hcut88 hcut35 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase000b hcase031a hcase010b hcase040b hcase020b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut30 hcut92 hcut9 hcut2 hcut82 hcut10 hcut0 hcut98 hcut11 hcut83 hcut4 hcut31 hcut65 hcut54 hcut62 hcut56 hcut60 hcut24 hcut52 hcut45 hcut61 hcut77 hcut97 hcut18 hcut95 hcut20 hcut50 hcut28 hcut33 hcut80 hcut51 hcut48 hcut55 hcut87 hcut47 hcut43 hcut13 hcut27 hcut75 hcut71 hcut88 hcut35 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase031a hcase010a hcase010b hcase040a hcase040b hcase021a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
          omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut30 hcut92 hcut9 hcut2 hcut82 hcut10 hcut0 hcut98 hcut11 hcut83 hcut4 hcut31 hcut65 hcut54 hcut62 hcut56 hcut60 hcut24 hcut52 hcut45 hcut61 hcut77 hcut97 hcut18 hcut95 hcut20 hcut50 hcut28 hcut33 hcut80 hcut51 hcut48 hcut55 hcut87 hcut47 hcut43 hcut13 hcut27 hcut75 hcut71 hcut88 hcut35 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase031a hcase010a hcase010b hcase041a hcase00 hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut30 hcut92 hcut9 hcut2 hcut82 hcut10 hcut0 hcut98 hcut11 hcut83 hcut4 hcut31 hcut65 hcut54 hcut62 hcut56 hcut60 hcut24 hcut52 hcut45 hcut61 hcut77 hcut97 hcut18 hcut95 hcut20 hcut50 hcut28 hcut33 hcut80 hcut51 hcut48 hcut55 hcut87 hcut47 hcut43 hcut13 hcut27 hcut75 hcut71 hcut88 hcut35 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase000a hcase000b hcase031a hcase011a hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega

#print axioms symbolic_v2_mask823_integer_shard000
end Jsp404.SixExactFloorKernel
