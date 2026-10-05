import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_mask75_integer_shard002 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut55 : (s11 + s12 + s14 + s30 + s31 + u11 + u12 + u14 + u30 + u31) + 1 ≤ (n))
    (hcut3 : (s02 + u02) + 1 ≤ (s12 + 2))
    (hcut81 : (s11 + s12 + s13 + s44 + u11 + u12 + u13 + u44) + 1 ≤ (n + 1))
    (hcut21 : (s30 + u30 + 2) + 1 ≤ (n))
    (hcut93 : (s03 + s31 + u03 + u31 + 1) + 1 ≤ (n))
    (hcut57 : (s31 + s32 + u31 + u32 + 1) + 1 ≤ (n))
    (hcut59 : (s12 + s30 + u12 + u30 + 1) + 1 ≤ (n))
    (hcut85 : (s12 + s13 + s30 + s44 + u12 + u13 + u30 + u44) + 1 ≤ (n + 1))
    (hcut90 : (s01 + s02 + s13 + s42 + s43 + u01 + u02 + u13 + u42 + u43) + 1 ≤ (s33 + 2))
    (hcut84 : (s11 + s13 + s30 + s44 + u11 + u13 + u30 + u44) + 1 ≤ (n + 1))
    (hcut70 : (s03 + u03 + 2) + 1 ≤ (n))
    (hcut1 : (s00 + s04 + s33 + s40 + s44 + u00 + u04 + u33 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut18 : (s11 + s14 + s31 + u11 + u14 + u31 + 2) + 1 ≤ (n))
    (hcut82 : (s13 + s30 + s44 + u13 + u30 + u44) + 1 ≤ (n))
    (hcut95 : (s31 + s32 + s33 + u31 + u32 + u33) + 1 ≤ (n))
    (hcut99 : (s03 + s41 + u03 + u41) + 1 ≤ (s13 + 2))
    (hcut100 : (s03 + s11 + s30 + u03 + u11 + u30) + 1 ≤ (n))
    (hcut42 : (s04 + s10 + s11 + s13 + s34 + s40 + u04 + u10 + u11 + u13 + u34 + u40) + 1 ≤ (2 * n + 1))
    (hcut97 : (s03 + s11 + u03 + u11 + 1) + 1 ≤ (n))
    (hcut101 : (s01 + s03 + s04 + u01 + u03 + u04) + 1 ≤ (n))
    (hcut87 : (s31 + s32 + s33 + s44 + u31 + u32 + u33 + u44) + 1 ≤ (n + 1))
    (hcut77 : (s40 + s41 + s43 + u40 + u41 + u43) + 1 ≤ (n))
    (hcut83 : (s13 + s31 + s44 + u13 + u31 + u44) + 1 ≤ (n))
    (hcut94 : (s03 + s12 + s30 + u03 + u12 + u30) + 1 ≤ (n))
    (hcut33 : (s00 + s34 + u00 + u34) + 1 ≤ (n + 1))
    (hcut16 : (s10 + s32 + u10 + u32) + 1 ≤ (n))
    (hcut0 : (s03 + s11 + s12 + s30 + s31 + s34 + s41 + s42 + s43 + u03 + u11 + u12 + u30 + u31 + u34 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut65 : (s01 + s02 + s42 + s43 + u01 + u02 + u42 + u43) + 1 ≤ (s33 + 1))
    (hcut58 : (s12 + s14 + u12 + u14 + 2) + 1 ≤ (n))
    (hcut73 : (s13 + s44 + u13 + u44 + 1) + 1 ≤ (n))
    (hcut92 : (s03 + s30 + u03 + u30 + 1) + 1 ≤ (n))
    (hcut49 : (s11 + s12 + u11 + u12 + 1) + 1 ≤ (n))
    (hcut15 : (s00 + s33 + u00 + u33) + 1 ≤ (n + 1))
    (hcut71 : (s10 + s11 + s44 + u10 + u11 + u44) + 1 ≤ (n))
    (hcut7 : (s00 + s33 + s34 + u00 + u33 + u34) + 1 ≤ (n + 2))
    (hcut44 : (s04 + s10 + s32 + s34 + s40 + u04 + u10 + u32 + u34 + u40) + 1 ≤ (2 * n + 1))
    (hcut102 : (s03 + s04 + s12 + u03 + u04 + u12 + 1) + 1 ≤ (n))
    (hcut40 : (s04 + s11 + s13 + s34 + s40 + u04 + u11 + u13 + u34 + u40) + 1 ≤ (2 * n))
    (hcut6 : (s02 + s10 + s13 + s14 + s32 + u02 + u10 + u13 + u14 + u32) + 1 ≤ (n + 1))
    (hcut17 : (s11 + s14 + s30 + u11 + u14 + u30 + 1) + 1 ≤ (n))
    (hcut98 : (s03 + s11 + s12 + u03 + u11 + u12) + 1 ≤ (n))
    (hcut76 : (s30 + s31 + u30 + u31) + 1 ≤ (s10 + 2))
    (hcut69 : (s00 + s04 + s33 + s40 + u00 + u04 + u33 + u40) + 1 ≤ (2 * n + 1))
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
    (hcase041a : 1 ≤ s04)
    (hcase041b : u04 = 1)
    (hcase331a : 1 ≤ s33)
    (hcase331b : u33 = 1)
    (hcase110a : s11 = 0)
    (hcase110b : u11 = 0)
    (hcase000a : s00 = 0)
    (hcase000b : u00 = 0)
    : False := by
  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
  ·
    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
    ·
      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut99 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase331b hcase110a hcase110b hcase000b hcase010b hcase020b hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega
    ·
      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut99 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase331b hcase110a hcase110b hcase000b hcase010b hcase021a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega
  ·
    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
    ·
      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
      ·
        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase331a hcase331b hcase110a hcase110b hcase000a hcase000b hcase030a hcase030b hcase440b hcase400b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43
          omega
        ·
          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
          ·
            clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut99 hcut100 hcut42 hcut97 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase331b hcase110a hcase110b hcase000b hcase011a hcase030a hcase030b hcase440a hcase440b hcase401a hcase401b hcase020b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43
            omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut99 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase110a hcase110b hcase000a hcase000b hcase011a hcase030b hcase440b hcase401a hcase021a hcase130a hcase130b hcase410b hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase331a hcase331b hcase110a hcase110b hcase000a hcase000b hcase011a hcase011b hcase030a hcase030b hcase440a hcase440b hcase401a hcase401b hcase021a hcase021b hcase130b hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43
                omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut84 hcut70 hcut18 hcut82 hcut95 hcut99 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase110a hcase110b hcase000a hcase000b hcase011a hcase030b hcase440a hcase440b hcase401a hcase021a hcase410b hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase110a hcase110b hcase000a hcase000b hcase011a hcase030a hcase030b hcase440b hcase401a hcase021a hcase131a hcase411a hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43
                omega
      ·
        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
        ·
          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
          ·
            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut99 hcut100 hcut42 hcut97 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase331b hcase110a hcase110b hcase000b hcase011a hcase030a hcase030b hcase441a hcase441b hcase130a hcase130b hcase410a hcase410b hcase020b hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase42 hcase43
              omega
            ·
              rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut99 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase331a hcase331b hcase110a hcase110b hcase000a hcase000b hcase011a hcase011b hcase030a hcase030b hcase441a hcase441b hcase130a hcase130b hcase410a hcase410b hcase120b hcase00 hcase04 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase42 hcase43
                omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut99 hcut100 hcut42 hcut97 hcut101 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase110a hcase110b hcase000b hcase011a hcase030a hcase030b hcase441a hcase130a hcase130b hcase410b hcase121a hcase400b hcase00 hcase04 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut18 hcut82 hcut95 hcut99 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase110a hcase110b hcase000a hcase000b hcase011a hcase030b hcase441a hcase130a hcase130b hcase410b hcase021a hcase121a hcase121b hcase401a hcase00 hcase04 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43
                  omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase331a hcase331b hcase110a hcase110b hcase000a hcase000b hcase011a hcase011b hcase030a hcase030b hcase441a hcase441b hcase130b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase42 hcase43
            omega
        ·
          rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
          ·
            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut99 hcut100 hcut42 hcut97 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase331b hcase110a hcase110b hcase000b hcase011a hcase030a hcase030b hcase441a hcase441b hcase131a hcase131b hcase120a hcase120b hcase020b hcase00 hcase04 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut99 hcut100 hcut42 hcut97 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase331b hcase110a hcase110b hcase000b hcase011a hcase030a hcase030b hcase441a hcase441b hcase131a hcase131b hcase120b hcase021a hcase00 hcase04 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43
              omega
          ·
            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut99 hcut100 hcut42 hcut97 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase331b hcase110a hcase110b hcase000b hcase011a hcase030a hcase030b hcase441a hcase441b hcase131a hcase131b hcase121a hcase121b hcase020b hcase00 hcase04 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43
              omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut100 hcut42 hcut97 hcut101 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase110a hcase110b hcase000b hcase011a hcase030a hcase030b hcase441a hcase131a hcase021a hcase400b hcase00 hcase04 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43
                omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut84 hcut70 hcut18 hcut82 hcut95 hcut99 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase110a hcase110b hcase000a hcase000b hcase011a hcase030b hcase441a hcase121a hcase121b hcase021a hcase401a hcase410b hcase00 hcase04 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut84 hcut70 hcut18 hcut82 hcut95 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase110a hcase110b hcase000a hcase000b hcase011a hcase030a hcase030b hcase441a hcase131a hcase121a hcase121b hcase021a hcase401a hcase411a hcase00 hcase04 hcase10 hcase11 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase43
                  omega
    ·
      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
      ·
        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut100 hcut42 hcut97 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase110a hcase110b hcase000b hcase400b hcase00 hcase02 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
        omega
      ·
        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
        ·
          clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut99 hcut100 hcut42 hcut97 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase331b hcase110a hcase110b hcase000b hcase011a hcase031a hcase401a hcase401b hcase020b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
          omega
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut90 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase331a hcase331b hcase110a hcase110b hcase000a hcase000b hcase011a hcase011b hcase401a hcase401b hcase021a hcase021b hcase130b hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut84 hcut70 hcut1 hcut18 hcut82 hcut95 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase110a hcase110b hcase000a hcase000b hcase011a hcase031a hcase401a hcase021a hcase131a hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut3 hcut81 hcut21 hcut93 hcut57 hcut59 hcut85 hcut84 hcut70 hcut18 hcut82 hcut95 hcut100 hcut42 hcut97 hcut101 hcut87 hcut77 hcut83 hcut94 hcut33 hcut16 hcut0 hcut65 hcut58 hcut73 hcut92 hcut49 hcut15 hcut71 hcut7 hcut44 hcut102 hcut40 hcut6 hcut17 hcut98 hcut76 hcut69 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase331a hcase110a hcase110b hcase000a hcase000b hcase011a hcase031a hcase401a hcase021a hcase131a hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase43
              omega

#print axioms symbolic_mask75_integer_shard002
end Jsp404.SixExactFloorKernel
