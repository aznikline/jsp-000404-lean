import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_mask127_integer_shard002 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut55 : (s30 + s32 + s33 + u30 + u32 + u33) + 1 ≤ (n))
    (hcut4 : (s02 + s03 + s10 + s14 + s32 + s33 + u02 + u03 + u10 + u14 + u32 + u33) + 1 ≤ (n + 1))
    (hcut46 : (s02 + s03 + s32 + u02 + u03 + u32 + 1) + 1 ≤ (n))
    (hcut52 : (s04 + s11 + s33 + u04 + u11 + u33 + 1) + 1 ≤ (n))
    (hcut53 : (s02 + s11 + s14 + u02 + u11 + u14 + 2) + 1 ≤ (n))
    (hcut8 : (s03 + u03) + 1 ≤ (s13 + 1))
    (hcut32 : (s30 + s32 + s34 + u30 + u32 + u34) + 1 ≤ (n))
    (hcut26 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut31 : (s31 + u31) + 1 ≤ (s10 + 1))
    (hcut48 : (s03 + s32 + s33 + u03 + u32 + u33 + 1) + 1 ≤ (n))
    (hcut58 : (s40 + s41 + s43 + s44 + u40 + u41 + u43 + u44) + 1 ≤ (n + 1))
    (hcut15 : (s40 + s41 + s42 + s43 + u40 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut59 : (s33 + s34 + s40 + s42 + u33 + u34 + u40 + u42) + 1 ≤ (n + 1))
    (hcut36 : (s01 + s30 + s34 + u01 + u30 + u34 + 1) + 1 ≤ (n))
    (hcut21 : (s03 + s32 + u03 + u32 + 2) + 1 ≤ (n))
    (hcut35 : (s30 + s31 + s33 + u30 + u31 + u33 + 1) + 1 ≤ (n))
    (hcut30 : (s34 + s40 + u34 + u40) + 1 ≤ (n))
    (hcut40 : (s02 + u02) + 1 ≤ (s34 + 1))
    (hcut27 : (s03 + s33 + u03 + u33 + 3) + 1 ≤ (n))
    (hcut13 : (s40 + s41 + s43 + u40 + u41 + u43) + 1 ≤ (n))
    (hcut50 : (s43 + s44 + u43 + u44 + 1) + 1 ≤ (n))
    (hcut16 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 2))
    (hcut22 : (s10 + s32 + u10 + u32 + 1) + 1 ≤ (n))
    (hcut33 : (s30 + s34 + u30 + u34 + 2) + 1 ≤ (n))
    (hcut51 : (s12 + s13 + s14 + u12 + u13 + u14 + 1) + 1 ≤ (n))
    (hcut0 : (s11 + s12 + s41 + s42 + u11 + u12 + u41 + u42) + 1 ≤ (s32 + 2))
    (hcut3 : (s00 + s04 + s13 + s40 + s44 + u00 + u04 + u13 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut45 : (s01 + s43 + u01 + u43) + 1 ≤ (s33 + 2))
    (hcut23 : (s14 + s32 + u14 + u32 + 1) + 1 ≤ (n))
    (hcut60 : (s40 + s41 + s42 + s44 + u40 + u41 + u42 + u44) + 1 ≤ (n + 1))
    (hcut42 : (s30 + s31 + u30 + u31) + 1 ≤ (s10 + 2))
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
    (hcase131a : 1 ≤ s13)
    (hcase131b : u13 = 1)
    (hcase330a : s33 = 0)
    (hcase330b : u33 = 0)
    : False := by
  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
  ·
    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
    ·
      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
      ·
        rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
        ·
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase040a hcase040b hcase100b hcase420a hcase420b hcase340b hcase300b hcase320b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase040a hcase040b hcase100b hcase420a hcase420b hcase340b hcase300b hcase321a hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase040a hcase040b hcase100b hcase420a hcase420b hcase340a hcase340b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase44
                    omega
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase040b hcase100a hcase100b hcase420b hcase020b hcase030b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330b hcase430b hcase410b hcase400b hcase010b hcase040b hcase100b hcase420b hcase341a hcase020b hcase031a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase44
                      omega
                  ·
                    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut27 hcut13 hcut50 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase040b hcase100a hcase100b hcase420b hcase341a hcase021a hcase030b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut55 hcut4 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330b hcase430b hcase410b hcase400b hcase010b hcase040b hcase100b hcase420b hcase341a hcase021a hcase031a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase44
                      omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase040a hcase040b hcase100a hcase100b hcase320b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase44
                  omega
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010a hcase010b hcase040a hcase040b hcase100a hcase100b hcase421a hcase321a hcase020a hcase020b hcase440b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase040b hcase100a hcase100b hcase421a hcase321a hcase020b hcase441a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34
                      omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010a hcase010b hcase040a hcase040b hcase100a hcase100b hcase421a hcase321a hcase321b hcase021a hcase021b hcase440b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase040b hcase100a hcase100b hcase421a hcase321a hcase021a hcase441a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34
                      omega
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase040a hcase040b hcase101a hcase101b hcase030a hcase030b hcase020a hcase020b hcase320b hcase300b hcase340b hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase42 hcase44
                        omega
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase040a hcase040b hcase101a hcase101b hcase030a hcase030b hcase020a hcase020b hcase320b hcase300a hcase300b hcase341a hcase310b hcase00 hcase11 hcase12 hcase13 hcase14 hcase33 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase040b hcase101a hcase101b hcase030b hcase020b hcase320b hcase300a hcase300b hcase341a hcase341b hcase00 hcase11 hcase12 hcase13 hcase14 hcase33 hcase42 hcase44
                          omega
                    ·
                      clear hn4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut51 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131b hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase040b hcase101a hcase101b hcase030b hcase020b hcase320b hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase34 hcase42 hcase44
                      omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase040b hcase030b hcase020b hcase420b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase040b hcase030b hcase020b hcase321a hcase421a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase44
                      omega
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase040a hcase040b hcase101a hcase101b hcase030a hcase030b hcase340b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase42 hcase44
                    omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut27 hcut13 hcut50 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase040b hcase101a hcase101b hcase030b hcase021a hcase341a hcase420b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase44
                      omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase040a hcase040b hcase101a hcase101b hcase030a hcase030b hcase021a hcase021b hcase341a hcase341b hcase320b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase44
                        omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010a hcase010b hcase040a hcase040b hcase030a hcase030b hcase341a hcase341b hcase421a hcase321a hcase440b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase040b hcase030a hcase030b hcase021a hcase341a hcase341b hcase421a hcase321a hcase441a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33
                          omega
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase040a hcase040b hcase101a hcase101b hcase031a hcase031b hcase310b hcase320b hcase300b hcase340b hcase00 hcase02 hcase11 hcase12 hcase13 hcase14 hcase33 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase040a hcase040b hcase101a hcase101b hcase031a hcase031b hcase310b hcase320b hcase300a hcase300b hcase341a hcase00 hcase02 hcase11 hcase12 hcase13 hcase14 hcase33 hcase42 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase040a hcase040b hcase101a hcase101b hcase031a hcase031b hcase310b hcase320b hcase301a hcase00 hcase02 hcase11 hcase12 hcase13 hcase14 hcase33 hcase34 hcase42 hcase44
                      omega
                  ·
                    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase040b hcase101a hcase101b hcase031a hcase310a hcase310b hcase020b hcase420b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase34 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase040b hcase101a hcase101b hcase031a hcase310a hcase310b hcase321a hcase020b hcase421a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase34 hcase44
                        omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase040b hcase031a hcase310a hcase310b hcase021a hcase420b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase34 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase040b hcase031a hcase310a hcase310b hcase321a hcase021a hcase421a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase34 hcase44
                        omega
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase040b hcase101a hcase101b hcase031a hcase020b hcase320b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase34 hcase42 hcase44
                      omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase040b hcase101a hcase101b hcase031a hcase020b hcase321a hcase321b hcase420b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase34 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase040b hcase101a hcase031a hcase020a hcase020b hcase321a hcase421a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33 hcase34 hcase44
                        omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase040b hcase101a hcase031a hcase021a hcase420b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase32 hcase33 hcase34 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase040b hcase101a hcase031a hcase021a hcase421a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase32 hcase33 hcase34 hcase44
                      omega
          ·
            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                  omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase141a hcase300b hcase310b hcase340b hcase00 hcase10 hcase11 hcase12 hcase13 hcase32 hcase33 hcase42 hcase44
                        omega
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase020a hcase020b hcase030a hcase030b hcase141a hcase141b hcase300a hcase300b hcase310b hcase341a hcase320b hcase00 hcase10 hcase11 hcase12 hcase13 hcase33 hcase42 hcase44
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase041a hcase020b hcase030b hcase141a hcase300a hcase300b hcase310a hcase310b hcase341a hcase341b hcase321a hcase321b hcase420b hcase00 hcase10 hcase11 hcase12 hcase13 hcase33 hcase44
                            omega
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase020a hcase020b hcase030a hcase030b hcase141a hcase141b hcase300a hcase300b hcase310a hcase310b hcase321a hcase321b hcase421a hcase440b hcase00 hcase10 hcase11 hcase12 hcase13 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase020b hcase030b hcase141a hcase300a hcase300b hcase310a hcase310b hcase341a hcase341b hcase321a hcase421a hcase441a hcase00 hcase10 hcase11 hcase12 hcase13 hcase33
                              omega
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase020a hcase020b hcase030a hcase030b hcase141a hcase141b hcase300a hcase300b hcase100b hcase00 hcase11 hcase12 hcase13 hcase32 hcase33 hcase34 hcase42 hcase44
                        omega
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          clear hn4 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase020b hcase030b hcase141a hcase141b hcase300a hcase300b hcase101a hcase101b hcase320b hcase00 hcase11 hcase12 hcase13 hcase33 hcase34 hcase42 hcase44
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase041a hcase020b hcase030b hcase141a hcase141b hcase300a hcase300b hcase101a hcase101b hcase321a hcase321b hcase420b hcase00 hcase11 hcase12 hcase13 hcase33 hcase34 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase020a hcase020b hcase030a hcase030b hcase141a hcase300a hcase300b hcase101a hcase321a hcase421a hcase00 hcase11 hcase12 hcase13 hcase33 hcase34 hcase44
                            omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase020a hcase020b hcase030a hcase030b hcase141a hcase141b hcase100b hcase00 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                      omega
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut51 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131b hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase020b hcase030b hcase141a hcase141b hcase101a hcase101b hcase320b hcase00 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42 hcase44
                        omega
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase141a hcase301a hcase101a hcase321a hcase340b hcase00 hcase11 hcase12 hcase13 hcase31 hcase33 hcase42 hcase44
                          omega
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase020a hcase020b hcase030a hcase030b hcase141a hcase141b hcase301a hcase101a hcase101b hcase321a hcase341a hcase310b hcase00 hcase11 hcase12 hcase13 hcase33 hcase42 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase020a hcase020b hcase030a hcase030b hcase141a hcase101a hcase321a hcase341a hcase311a hcase00 hcase11 hcase12 hcase13 hcase33 hcase42 hcase44
                            omega
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase320a hcase320b hcase140b hcase00 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase020b hcase031a hcase100b hcase320b hcase141a hcase00 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                      omega
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase020a hcase020b hcase031a hcase031b hcase100a hcase100b hcase321a hcase321b hcase110a hcase110b hcase140b hcase00 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase020a hcase020b hcase031a hcase031b hcase100b hcase321a hcase321b hcase110b hcase141a hcase00 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                        omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase041a hcase020b hcase031a hcase100a hcase100b hcase321a hcase321b hcase111b hcase420b hcase00 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase44
                        omega
                      ·
                        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase020b hcase031a hcase100a hcase100b hcase321a hcase421a hcase140b hcase00 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase020a hcase020b hcase031a hcase100a hcase100b hcase321a hcase421a hcase141a hcase00 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase44
                          omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase140b hcase00 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                    omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase020a hcase020b hcase101a hcase101b hcase141b hcase320b hcase300b hcase340b hcase00 hcase11 hcase12 hcase13 hcase31 hcase33 hcase42 hcase44
                          omega
                        ·
                          rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase020a hcase020b hcase031a hcase031b hcase101a hcase101b hcase141a hcase141b hcase320b hcase300a hcase300b hcase341a hcase310b hcase00 hcase11 hcase12 hcase13 hcase33 hcase42 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase020b hcase031a hcase101a hcase101b hcase141a hcase141b hcase320b hcase300a hcase300b hcase341a hcase341b hcase00 hcase11 hcase12 hcase13 hcase33 hcase42 hcase44
                            omega
                      ·
                        clear hn4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut51 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase020b hcase031a hcase101a hcase101b hcase141a hcase141b hcase320b hcase00 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase42 hcase44
                        omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase041a hcase020a hcase020b hcase031a hcase141a hcase420b hcase00 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase020a hcase020b hcase031a hcase141a hcase321a hcase421a hcase00 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase44
                        omega
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase021a hcase021b hcase100a hcase100b hcase140b hcase00 hcase03 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                  omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase021a hcase021b hcase100b hcase141a hcase320a hcase320b hcase110b hcase00 hcase03 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase021a hcase021b hcase100a hcase100b hcase141a hcase141b hcase320b hcase00 hcase03 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                      omega
                  ·
                    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase041a hcase021a hcase100a hcase100b hcase141a hcase321a hcase321b hcase030b hcase420b hcase00 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase44
                        omega
                      ·
                        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase021a hcase021b hcase100b hcase141a hcase321a hcase321b hcase030a hcase030b hcase421a hcase421b hcase110b hcase00 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase021a hcase100a hcase100b hcase141a hcase321a hcase030a hcase030b hcase421a hcase111a hcase00 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase44
                          omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase021a hcase021b hcase100b hcase141a hcase321a hcase321b hcase031a hcase031b hcase110b hcase00 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase021a hcase100a hcase100b hcase141a hcase321a hcase031a hcase111a hcase00 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                        omega
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase101a hcase300b hcase340b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase32 hcase33 hcase42 hcase44
                    omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase021a hcase021b hcase101a hcase101b hcase300a hcase300b hcase341a hcase341b hcase140b hcase00 hcase03 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase42 hcase44
                      omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase021a hcase021b hcase101a hcase101b hcase300a hcase300b hcase341a hcase141a hcase141b hcase310b hcase320b hcase00 hcase03 hcase11 hcase12 hcase13 hcase33 hcase42 hcase44
                          omega
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase041a hcase021a hcase300a hcase300b hcase341a hcase341b hcase141a hcase310a hcase310b hcase420b hcase00 hcase03 hcase11 hcase12 hcase13 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase021a hcase300a hcase300b hcase341a hcase341b hcase141a hcase310a hcase310b hcase321a hcase421a hcase00 hcase03 hcase11 hcase12 hcase13 hcase33 hcase44
                            omega
                      ·
                        rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase400b hcase010b hcase041a hcase021a hcase101a hcase300a hcase300b hcase341a hcase341b hcase141a hcase320a hcase320b hcase420b hcase00 hcase03 hcase11 hcase12 hcase13 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase021a hcase021b hcase101a hcase101b hcase300a hcase300b hcase341a hcase341b hcase141a hcase141b hcase311a hcase311b hcase320b hcase00 hcase03 hcase11 hcase12 hcase13 hcase33 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase021a hcase101a hcase300a hcase300b hcase341a hcase341b hcase141a hcase321a hcase00 hcase03 hcase11 hcase12 hcase13 hcase33 hcase42 hcase44
                          omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase021a hcase021b hcase101a hcase101b hcase301a hcase301b hcase140b hcase00 hcase03 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                    omega
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase021a hcase021b hcase101a hcase101b hcase301a hcase141a hcase141b hcase310b hcase320b hcase00 hcase03 hcase11 hcase12 hcase13 hcase33 hcase34 hcase42 hcase44
                        omega
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase101a hcase101b hcase301a hcase301b hcase141a hcase141b hcase310a hcase310b hcase321a hcase321b hcase340b hcase00 hcase03 hcase11 hcase12 hcase13 hcase33 hcase42 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase010a hcase010b hcase041a hcase041b hcase021a hcase021b hcase101a hcase101b hcase301a hcase141a hcase141b hcase310b hcase321a hcase341a hcase00 hcase03 hcase11 hcase12 hcase13 hcase33 hcase42 hcase44
                          omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase400b hcase010b hcase041a hcase021a hcase101a hcase141a hcase00 hcase03 hcase11 hcase12 hcase13 hcase32 hcase33 hcase34 hcase42 hcase44
                      omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase400a hcase400b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
          omega
      ·
        rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase320b hcase340b hcase300b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase42 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase320b hcase340b hcase301a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase42 hcase44
                omega
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase320b hcase341a hcase300a hcase300b hcase310b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase42 hcase44
                  omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase320b hcase341a hcase300b hcase311a hcase420a hcase420b hcase040a hcase040b hcase440b hcase00 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33
                        omega
                      ·
                        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                        ·
                          clear hn4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010b hcase320b hcase341a hcase300b hcase311a hcase420b hcase040b hcase441a hcase020b hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33
                          omega
                        ·
                          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase320a hcase320b hcase341a hcase300a hcase300b hcase311a hcase311b hcase420b hcase040b hcase441a hcase021a hcase030b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33
                            omega
                          ·
                            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase320b hcase341a hcase300a hcase300b hcase311a hcase420a hcase420b hcase040a hcase040b hcase441a hcase441b hcase021a hcase021b hcase031a hcase031b hcase100b hcase00 hcase11 hcase12 hcase13 hcase14 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase320a hcase320b hcase341a hcase300b hcase311a hcase420b hcase040b hcase441a hcase021a hcase031a hcase101a hcase00 hcase11 hcase12 hcase13 hcase14 hcase33
                              omega
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase320b hcase341a hcase300a hcase300b hcase311a hcase420a hcase420b hcase041a hcase041b hcase100b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                        omega
                      ·
                        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                        ·
                          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                          ·
                            clear hn4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010b hcase320b hcase341a hcase300b hcase311a hcase420b hcase041a hcase101a hcase101b hcase020b hcase030b hcase00 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010b hcase320b hcase341a hcase300b hcase311a hcase420b hcase041a hcase101a hcase101b hcase020b hcase031a hcase00 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                            omega
                        ·
                          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase320a hcase320b hcase341a hcase341b hcase300a hcase300b hcase311a hcase311b hcase420a hcase420b hcase101a hcase101b hcase021a hcase021b hcase140b hcase00 hcase03 hcase11 hcase12 hcase13 hcase33 hcase44
                            omega
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131b hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase320b hcase341a hcase300b hcase311a hcase420b hcase101a hcase101b hcase021a hcase021b hcase141a hcase141b hcase440b hcase00 hcase03 hcase11 hcase12 hcase13 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase320a hcase320b hcase341a hcase300b hcase311a hcase420b hcase041a hcase101a hcase021a hcase141a hcase441a hcase00 hcase03 hcase11 hcase12 hcase13 hcase33
                              omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase320b hcase341a hcase341b hcase300a hcase300b hcase311a hcase311b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                    omega
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase320b hcase341a hcase420a hcase420b hcase100b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase44
                    omega
                  ·
                    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase320b hcase341a hcase301a hcase420a hcase420b hcase101a hcase101b hcase020a hcase020b hcase310b hcase00 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                        omega
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                          ·
                            clear hn4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010b hcase320b hcase341a hcase301a hcase420b hcase101a hcase101b hcase020b hcase311a hcase040b hcase030b hcase00 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010b hcase320b hcase341a hcase301a hcase420b hcase101a hcase101b hcase020b hcase311a hcase040b hcase031a hcase00 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                            omega
                        ·
                          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                          ·
                            clear hn4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010b hcase320b hcase341a hcase301a hcase420b hcase101a hcase101b hcase020b hcase311a hcase041a hcase030b hcase00 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010b hcase320b hcase341a hcase301a hcase420b hcase101a hcase101b hcase020b hcase311a hcase041a hcase031a hcase00 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                            omega
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase320a hcase320b hcase301a hcase301b hcase420b hcase101a hcase101b hcase021a hcase021b hcase140a hcase140b hcase040a hcase040b hcase440b hcase00 hcase03 hcase11 hcase12 hcase13 hcase31 hcase33
                            omega
                          ·
                            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase320a hcase320b hcase341a hcase301a hcase301b hcase420b hcase101a hcase101b hcase021a hcase140a hcase140b hcase040b hcase441a hcase030b hcase00 hcase11 hcase12 hcase13 hcase31 hcase33
                              omega
                            ·
                              rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase320b hcase341a hcase301a hcase420a hcase420b hcase101a hcase101b hcase021a hcase021b hcase140a hcase140b hcase040a hcase040b hcase441a hcase441b hcase031a hcase031b hcase310b hcase00 hcase11 hcase12 hcase13 hcase33
                                omega
                              ·
                                clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase320a hcase320b hcase341a hcase301a hcase420b hcase101a hcase021a hcase140a hcase140b hcase040b hcase441a hcase031a hcase311a hcase00 hcase11 hcase12 hcase13 hcase33
                                omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase320a hcase320b hcase341a hcase341b hcase301a hcase301b hcase420a hcase420b hcase101a hcase101b hcase021a hcase021b hcase140b hcase00 hcase03 hcase11 hcase12 hcase13 hcase31 hcase33 hcase44
                          omega
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase320b hcase341a hcase301a hcase420a hcase420b hcase101a hcase101b hcase021a hcase021b hcase141a hcase141b hcase310b hcase00 hcase03 hcase04 hcase11 hcase12 hcase13 hcase33 hcase44
                          omega
                        ·
                          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                          ·
                            clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase320a hcase320b hcase341a hcase301a hcase420b hcase101a hcase021a hcase311a hcase040b hcase00 hcase03 hcase11 hcase12 hcase13 hcase33 hcase44
                            omega
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131b hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase320b hcase341a hcase301a hcase420b hcase101a hcase101b hcase021a hcase021b hcase141b hcase311a hcase041a hcase041b hcase440b hcase00 hcase03 hcase11 hcase12 hcase13 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase320a hcase320b hcase341a hcase301a hcase420b hcase101a hcase021a hcase141a hcase311a hcase041a hcase441a hcase00 hcase03 hcase11 hcase12 hcase13 hcase33
                              omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase320b hcase341a hcase341b hcase301a hcase301b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase44
                  omega
          ·
            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase100b hcase340b hcase300b hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase100b hcase340b hcase301a hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase44
                          omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase321b hcase420b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase100a hcase100b hcase440b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase321b hcase420b hcase040b hcase020b hcase030b hcase100a hcase100b hcase441a hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33
                          omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase101a hcase340b hcase300b hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase101a hcase340b hcase301a hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase44
                          omega
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                          ·
                            clear hn4 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase040b hcase020b hcase030b hcase341a hcase310b hcase300b hcase00 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase101a hcase101b hcase341a hcase310b hcase301a hcase00 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                            omega
                        ·
                          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                          ·
                            clear hn4 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase040b hcase020b hcase030b hcase101a hcase341a hcase311a hcase300b hcase00 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase040b hcase020b hcase030b hcase101a hcase341a hcase311a hcase301a hcase00 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                            omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase420b hcase040a hcase040b hcase020a hcase020b hcase440b hcase100b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34
                        omega
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase420b hcase040a hcase040b hcase020a hcase020b hcase440b hcase101a hcase300b hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase34
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase420b hcase040a hcase040b hcase020a hcase020b hcase440b hcase101a hcase301a hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase34
                          omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase020a hcase020b hcase441a hcase441b hcase310a hcase310b hcase340b hcase100b hcase00 hcase11 hcase12 hcase13 hcase14 hcase30 hcase33
                            omega
                          ·
                            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase020a hcase020b hcase441a hcase441b hcase310b hcase340b hcase101a hcase101b hcase300b hcase00 hcase11 hcase12 hcase13 hcase14 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase020a hcase020b hcase441a hcase441b hcase310a hcase310b hcase340b hcase101a hcase301a hcase00 hcase11 hcase12 hcase13 hcase14 hcase33
                              omega
                        ·
                          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                          ·
                            clear hn4 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase040b hcase020b hcase031a hcase441a hcase310b hcase341a hcase300b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase020a hcase020b hcase031a hcase031b hcase441a hcase441b hcase310b hcase341a hcase301a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33
                            omega
                      ·
                        rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                        ·
                          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase020a hcase020b hcase441a hcase441b hcase311a hcase300b hcase340b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase33
                            omega
                          ·
                            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase321b hcase420a hcase420b hcase040a hcase040b hcase020a hcase020b hcase031a hcase031b hcase441a hcase441b hcase300a hcase300b hcase341a hcase341b hcase100b hcase00 hcase11 hcase12 hcase13 hcase14 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase040b hcase020a hcase020b hcase031a hcase441a hcase311a hcase300b hcase341a hcase101a hcase00 hcase11 hcase12 hcase13 hcase14 hcase33
                              omega
                        ·
                          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase321b hcase420a hcase420b hcase040a hcase040b hcase020a hcase020b hcase031a hcase031b hcase441a hcase441b hcase100b hcase00 hcase11 hcase12 hcase13 hcase14 hcase33 hcase34
                            omega
                          ·
                            rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase020a hcase020b hcase441a hcase441b hcase311a hcase301a hcase101a hcase340b hcase00 hcase11 hcase12 hcase13 hcase14 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase040b hcase020a hcase020b hcase031a hcase441a hcase311a hcase301a hcase101a hcase341a hcase00 hcase11 hcase12 hcase13 hcase14 hcase33
                              omega
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase100b hcase300b hcase340b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase44
                        omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut4 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase420b hcase040a hcase040b hcase100b hcase300b hcase341a hcase440b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut55 hcut4 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase040b hcase021a hcase100b hcase300b hcase341a hcase441a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase321b hcase420a hcase420b hcase040a hcase040b hcase021a hcase021b hcase100b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase34 hcase44
                      omega
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase300b hcase310b hcase340b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                          omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase300b hcase310b hcase341a hcase440b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase040b hcase021a hcase300b hcase310b hcase341a hcase441a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33
                            omega
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase101a hcase300b hcase311a hcase340b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                          omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase420b hcase040a hcase040b hcase101a hcase300b hcase311a hcase341a hcase440b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase040b hcase021a hcase101a hcase300b hcase311a hcase341a hcase441a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33
                            omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase040a hcase040b hcase101a hcase301a hcase340b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase44
                        omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut36 hcut21 hcut35 hcut30 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase321b hcase420a hcase420b hcase040a hcase040b hcase101a hcase101b hcase301a hcase301b hcase341a hcase440b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33
                          omega
                        ·
                          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase321b hcase420b hcase040b hcase021a hcase101a hcase101b hcase301a hcase301b hcase341a hcase441a hcase030b hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase040b hcase021a hcase101a hcase301a hcase341a hcase441a hcase031a hcase00 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33
                            omega
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase321b hcase420a hcase420b hcase100a hcase100b hcase140b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase44
                    omega
                  ·
                    rcases hcase12 with ⟨hcase120a, hcase120b⟩ | ⟨hcase121a, hcase121b⟩
                    ·
                      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                      ·
                        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                        ·
                          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                          ·
                            clear hn4 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut45 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase420b hcase041a hcase100b hcase141a hcase120b hcase030b hcase020b hcase110b hcase00 hcase13 hcase30 hcase31 hcase33 hcase34 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase321b hcase420b hcase041a hcase100b hcase141a hcase120b hcase030b hcase020a hcase020b hcase111a hcase00 hcase13 hcase30 hcase31 hcase33 hcase34 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase321b hcase420b hcase041a hcase100b hcase141a hcase120b hcase030b hcase021a hcase00 hcase11 hcase13 hcase30 hcase31 hcase33 hcase34 hcase44
                          omega
                      ·
                        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                        ·
                          rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase420b hcase041a hcase041b hcase100b hcase141a hcase141b hcase120a hcase120b hcase020a hcase020b hcase300b hcase440b hcase00 hcase11 hcase13 hcase31 hcase33 hcase34
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase321b hcase420b hcase041a hcase100a hcase100b hcase141a hcase141b hcase120a hcase120b hcase031a hcase020b hcase300a hcase300b hcase441a hcase00 hcase11 hcase13 hcase31 hcase33 hcase34
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase321b hcase420a hcase420b hcase041a hcase041b hcase100b hcase141a hcase141b hcase120a hcase120b hcase031a hcase031b hcase020a hcase020b hcase00 hcase11 hcase13 hcase31 hcase33 hcase34 hcase44
                            omega
                        ·
                          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                          ·
                            clear hn4 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase420b hcase041a hcase100a hcase100b hcase141a hcase120b hcase031a hcase021a hcase110b hcase00 hcase13 hcase30 hcase31 hcase33 hcase34 hcase44
                            omega
                          ·
                            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                            ·
                              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase041a hcase041b hcase100a hcase100b hcase120a hcase120b hcase111a hcase111b hcase300b hcase340b hcase00 hcase13 hcase31 hcase33 hcase44
                                omega
                              ·
                                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                                ·
                                  clear hn4 hcut55 hcut46 hcut52 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase041a hcase100b hcase120b hcase031a hcase111a hcase300b hcase341a hcase440b hcase00 hcase13 hcase31 hcase33
                                  omega
                                ·
                                  clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase041a hcase100a hcase100b hcase141a hcase120a hcase120b hcase031a hcase021a hcase111a hcase111b hcase300b hcase341a hcase441a hcase00 hcase13 hcase31 hcase33
                                  omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase321b hcase420a hcase420b hcase041a hcase041b hcase100b hcase141a hcase141b hcase120a hcase120b hcase031a hcase031b hcase021a hcase021b hcase111a hcase111b hcase00 hcase13 hcase31 hcase33 hcase34 hcase44
                              omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase321b hcase420a hcase420b hcase041a hcase041b hcase100b hcase141a hcase121a hcase110b hcase00 hcase02 hcase03 hcase13 hcase30 hcase31 hcase33 hcase34 hcase44
                        omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase420b hcase041a hcase041b hcase100b hcase121a hcase121b hcase111a hcase111b hcase440b hcase00 hcase02 hcase03 hcase13 hcase30 hcase31 hcase33 hcase34
                          omega
                        ·
                          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                          ·
                            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                            ·
                              clear hn4 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut45 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase410a hcase410b hcase401a hcase010b hcase321a hcase420a hcase420b hcase041a hcase100b hcase141a hcase121a hcase111a hcase441a hcase020b hcase030b hcase00 hcase13 hcase30 hcase31 hcase33 hcase34
                              omega
                            ·
                              clear hn4 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase410a hcase410b hcase401a hcase010b hcase321a hcase420a hcase420b hcase041a hcase100a hcase100b hcase141a hcase121a hcase111a hcase441a hcase020a hcase020b hcase031a hcase00 hcase13 hcase30 hcase31 hcase33 hcase34
                              omega
                          ·
                            clear hn4 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase410a hcase410b hcase401a hcase010b hcase321a hcase420a hcase420b hcase041a hcase100a hcase100b hcase141a hcase121a hcase111a hcase441a hcase021a hcase00 hcase03 hcase13 hcase30 hcase31 hcase33 hcase34
                            omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase101a hcase101b hcase300b hcase310b hcase340b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                        omega
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase420b hcase041a hcase041b hcase300b hcase310b hcase341a hcase440b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33
                          omega
                        ·
                          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                          ·
                            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase321b hcase420b hcase041a hcase101a hcase101b hcase300a hcase300b hcase310a hcase310b hcase341a hcase341b hcase441a hcase020b hcase030b hcase00 hcase11 hcase12 hcase13 hcase14 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase321b hcase420b hcase041a hcase101a hcase101b hcase300a hcase300b hcase310a hcase310b hcase341a hcase341b hcase441a hcase020b hcase031a hcase00 hcase11 hcase12 hcase13 hcase14 hcase33
                              omega
                          ·
                            clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase041a hcase300b hcase310b hcase341a hcase441a hcase021a hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33
                            omega
                    ·
                      rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                      ·
                        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                        ·
                          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase321b hcase420a hcase420b hcase101a hcase101b hcase300a hcase300b hcase311a hcase311b hcase020a hcase020b hcase030a hcase030b hcase140b hcase00 hcase11 hcase12 hcase13 hcase33 hcase34 hcase44
                            omega
                          ·
                            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase420b hcase101a hcase300b hcase311a hcase020a hcase020b hcase030a hcase030b hcase141a hcase440b hcase00 hcase11 hcase12 hcase13 hcase33 hcase34
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase321b hcase420b hcase041a hcase101a hcase101b hcase300a hcase300b hcase311a hcase311b hcase020b hcase030b hcase141a hcase141b hcase441a hcase00 hcase11 hcase12 hcase13 hcase33 hcase34
                              omega
                        ·
                          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase101a hcase300b hcase311a hcase020a hcase020b hcase340b hcase00 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                            omega
                          ·
                            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase321b hcase420a hcase420b hcase101a hcase101b hcase300a hcase300b hcase311a hcase311b hcase020a hcase020b hcase031a hcase031b hcase341a hcase341b hcase140b hcase00 hcase11 hcase12 hcase13 hcase33 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase041a hcase101a hcase300b hcase311a hcase020a hcase020b hcase031a hcase341a hcase141a hcase00 hcase11 hcase12 hcase13 hcase33 hcase44
                              omega
                      ·
                        rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase101a hcase300b hcase311a hcase340b hcase00 hcase03 hcase11 hcase12 hcase13 hcase14 hcase33 hcase44
                          omega
                        ·
                          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase321b hcase420a hcase420b hcase101a hcase101b hcase300a hcase300b hcase311a hcase311b hcase021a hcase021b hcase341a hcase341b hcase140b hcase00 hcase03 hcase11 hcase12 hcase13 hcase33 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase041a hcase101a hcase300b hcase311a hcase021a hcase341a hcase141a hcase00 hcase03 hcase11 hcase12 hcase13 hcase33 hcase44
                            omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase321b hcase420a hcase420b hcase101a hcase101b hcase301a hcase301b hcase140b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase44
                      omega
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase041a hcase041b hcase101a hcase301a hcase340b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase31 hcase33 hcase44
                        omega
                      ·
                        rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase010a hcase010b hcase321a hcase420a hcase420b hcase041a hcase041b hcase101a hcase101b hcase301a hcase141a hcase141b hcase341a hcase310b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase33 hcase44
                          omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase420b hcase041a hcase041b hcase101a hcase301a hcase341a hcase311a hcase440b hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase33
                            omega
                          ·
                            clear hn4 hsum_nat1 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010b hcase321a hcase420b hcase041a hcase101a hcase301a hcase141a hcase341a hcase311a hcase441a hcase00 hcase02 hcase03 hcase11 hcase12 hcase13 hcase33
                            omega
            ·
              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase421a hcase440b hcase100b hcase300b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase34
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase421a hcase440b hcase100b hcase301a hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase34
                    omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase421a hcase440b hcase101a hcase300b hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase34
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410b hcase401a hcase010a hcase010b hcase321a hcase421a hcase440b hcase101a hcase301a hcase00 hcase02 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase34
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase410a hcase410b hcase401a hcase010a hcase010b hcase321a hcase321b hcase421a hcase441a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34
                omega
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase410a hcase410b hcase401a hcase401b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
          omega
    ·
      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
      ·
        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
        ·
          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131b hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140a hcase140b hcase300b hcase340b hcase320b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase33 hcase40 hcase42 hcase44
                    omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140a hcase140b hcase300b hcase340b hcase321a hcase100b hcase00 hcase04 hcase11 hcase12 hcase13 hcase31 hcase33 hcase40 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140a hcase140b hcase300b hcase340b hcase321a hcase101a hcase00 hcase04 hcase11 hcase12 hcase13 hcase31 hcase33 hcase40 hcase42 hcase44
                      omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140a hcase140b hcase300a hcase300b hcase341b hcase400b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase42
                      omega
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        clear hn4 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010b hcase020b hcase030b hcase140a hcase140b hcase300a hcase300b hcase341b hcase400b hcase441a hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010b hcase020b hcase030b hcase140b hcase300a hcase300b hcase341b hcase400b hcase441a hcase041a hcase00 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase42
                        omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140a hcase140b hcase300a hcase300b hcase341a hcase341b hcase401a hcase440b hcase420b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140a hcase140b hcase300a hcase300b hcase341a hcase341b hcase401a hcase440b hcase421a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140a hcase140b hcase300a hcase300b hcase341a hcase341b hcase401a hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase42
                      omega
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140a hcase140b hcase100b hcase00 hcase04 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase34 hcase40 hcase42 hcase44
                  omega
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140a hcase140b hcase301a hcase301b hcase101a hcase101b hcase320b hcase00 hcase04 hcase11 hcase12 hcase13 hcase31 hcase33 hcase34 hcase40 hcase42 hcase44
                    omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140a hcase140b hcase301a hcase101a hcase321a hcase340b hcase00 hcase04 hcase11 hcase12 hcase13 hcase31 hcase33 hcase40 hcase42 hcase44
                      omega
                    ·
                      rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140a hcase140b hcase301a hcase101a hcase101b hcase321a hcase341a hcase310b hcase00 hcase04 hcase11 hcase12 hcase13 hcase33 hcase40 hcase42 hcase44
                        omega
                      ·
                        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010b hcase020b hcase030b hcase140b hcase101a hcase321a hcase341a hcase341b hcase400b hcase00 hcase04 hcase11 hcase12 hcase13 hcase33 hcase42 hcase44
                          omega
                        ·
                          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140a hcase140b hcase301a hcase301b hcase101a hcase101b hcase321a hcase321b hcase341a hcase341b hcase311a hcase311b hcase401a hcase440b hcase420b hcase00 hcase04 hcase11 hcase12 hcase13 hcase33
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140a hcase140b hcase301a hcase301b hcase101a hcase101b hcase321a hcase321b hcase341a hcase341b hcase311a hcase311b hcase401a hcase440b hcase421a hcase00 hcase04 hcase11 hcase12 hcase13 hcase33
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase140a hcase140b hcase301a hcase301b hcase101a hcase101b hcase321a hcase321b hcase341a hcase341b hcase311a hcase311b hcase401a hcase441a hcase00 hcase04 hcase11 hcase12 hcase13 hcase33 hcase42
                            omega
            ·
              rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  rcases hcase31 with ⟨hcase310a, hcase310b⟩ | ⟨hcase311a, hcase311b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase340b hcase300b hcase310b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase32 hcase33 hcase40 hcase42 hcase44
                    omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase141a hcase141b hcase340a hcase340b hcase300a hcase300b hcase100b hcase00 hcase04 hcase11 hcase12 hcase13 hcase32 hcase33 hcase40 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase340b hcase300b hcase311a hcase101a hcase00 hcase04 hcase11 hcase12 hcase13 hcase32 hcase33 hcase40 hcase42 hcase44
                      omega
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase141a hcase141b hcase340a hcase340b hcase100b hcase00 hcase04 hcase11 hcase12 hcase13 hcase31 hcase32 hcase33 hcase40 hcase42 hcase44
                    omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131b hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase141b hcase340b hcase301a hcase101a hcase101b hcase320b hcase00 hcase04 hcase11 hcase12 hcase13 hcase31 hcase33 hcase40 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase340b hcase301a hcase101a hcase321a hcase00 hcase04 hcase11 hcase12 hcase13 hcase31 hcase33 hcase40 hcase42 hcase44
                      omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase141a hcase141b hcase341a hcase341b hcase320b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase40 hcase42 hcase44
                  omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase141a hcase141b hcase341b hcase321a hcase321b hcase400b hcase440b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase42
                      omega
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010b hcase020b hcase030b hcase341a hcase341b hcase321a hcase400b hcase441a hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010b hcase020b hcase030b hcase141a hcase341a hcase341b hcase321a hcase400b hcase441a hcase041a hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase42
                        omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase141a hcase141b hcase341a hcase341b hcase321a hcase321b hcase401a hcase440b hcase420b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase141a hcase141b hcase341a hcase341b hcase321a hcase321b hcase401a hcase440b hcase421a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010a hcase010b hcase020a hcase020b hcase030a hcase030b hcase141a hcase141b hcase341a hcase341b hcase321a hcase321b hcase401a hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase42
                      omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase010a hcase010b hcase020a hcase020b hcase031a hcase031b hcase400a hcase400b hcase040a hcase040b hcase320b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010b hcase020b hcase031a hcase400b hcase040b hcase321a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                  omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase010a hcase010b hcase020a hcase020b hcase031a hcase031b hcase400a hcase400b hcase041a hcase041b hcase320b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                  omega
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase031a hcase031b hcase400a hcase400b hcase321a hcase321b hcase100a hcase100b hcase140b hcase00 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                      omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase330a hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase031a hcase031b hcase400a hcase400b hcase041a hcase041b hcase321a hcase321b hcase100b hcase141a hcase110b hcase00 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase411a hcase010b hcase020a hcase020b hcase031a hcase400b hcase041a hcase321a hcase100a hcase100b hcase141a hcase111a hcase00 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                        omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase020a hcase020b hcase031a hcase031b hcase400a hcase400b hcase321a hcase321b hcase101a hcase101b hcase140b hcase00 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010b hcase020a hcase020b hcase031a hcase400b hcase041a hcase321a hcase141a hcase00 hcase11 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                      omega
            ·
              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase010a hcase010b hcase020a hcase020b hcase031a hcase031b hcase401a hcase440b hcase420b hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase010a hcase010b hcase020a hcase020b hcase031a hcase031b hcase401a hcase440b hcase421a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010a hcase010b hcase020a hcase020b hcase031a hcase031b hcase401a hcase441a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42
                omega
        ·
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010a hcase010b hcase040a hcase040b hcase400b hcase030a hcase030b hcase440b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42
                  omega
                ·
                  clear hn4 hsum_nat1 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010b hcase021a hcase040b hcase400b hcase030b hcase441a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42
                  omega
              ·
                rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase010a hcase010b hcase021a hcase021b hcase040a hcase040b hcase400a hcase400b hcase031a hcase031b hcase320b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010b hcase021a hcase040b hcase400b hcase031a hcase321a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                  omega
            ·
              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase010a hcase010b hcase021a hcase021b hcase040a hcase040b hcase401a hcase440b hcase420b hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase010a hcase010b hcase021a hcase021b hcase040a hcase040b hcase401a hcase440b hcase421a hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010a hcase010b hcase021a hcase021b hcase040a hcase040b hcase401a hcase441a hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42
                omega
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase021a hcase021b hcase110a hcase110b hcase140b hcase00 hcase03 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase42 hcase44
                omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase010a hcase010b hcase021a hcase021b hcase041a hcase041b hcase110a hcase110b hcase141a hcase141b hcase400a hcase400b hcase320b hcase00 hcase03 hcase10 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                    omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase330a hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase021a hcase021b hcase041a hcase041b hcase110b hcase141a hcase400a hcase400b hcase321a hcase321b hcase100b hcase00 hcase03 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase411a hcase010b hcase021a hcase041a hcase110a hcase110b hcase141a hcase400b hcase321a hcase101a hcase00 hcase03 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                      omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase010a hcase010b hcase021a hcase021b hcase041a hcase041b hcase110a hcase110b hcase141a hcase141b hcase401a hcase440b hcase420b hcase00 hcase03 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase010a hcase010b hcase021a hcase021b hcase041a hcase041b hcase110a hcase110b hcase141a hcase141b hcase401a hcase440b hcase421a hcase00 hcase03 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010a hcase010b hcase021a hcase021b hcase041a hcase041b hcase110a hcase110b hcase141a hcase141b hcase401a hcase441a hcase00 hcase03 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42
                    omega
            ·
              rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase010a hcase010b hcase021a hcase021b hcase041a hcase041b hcase320b hcase00 hcase03 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase42 hcase44
                omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010b hcase021a hcase041a hcase321a hcase400b hcase140b hcase00 hcase03 hcase10 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut22 hcut33 hcut51 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase131b hcase330a hcase330b hcase430b hcase411a hcase010b hcase021a hcase041a hcase321a hcase400b hcase141a hcase00 hcase03 hcase10 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                    omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase411b hcase010a hcase010b hcase021a hcase021b hcase111a hcase111b hcase321a hcase321b hcase401a hcase401b hcase140b hcase00 hcase03 hcase10 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42 hcase44
                    omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase010a hcase010b hcase021a hcase021b hcase041a hcase041b hcase111a hcase111b hcase321a hcase321b hcase401a hcase141a hcase141b hcase440b hcase420b hcase00 hcase03 hcase10 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330a hcase330b hcase430a hcase430b hcase411a hcase010a hcase010b hcase021a hcase021b hcase041a hcase041b hcase111a hcase111b hcase321a hcase321b hcase401a hcase141a hcase141b hcase440b hcase421a hcase00 hcase03 hcase10 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34
                        omega
                    ·
                      clear hn4 hsum_nat3 hcut55 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut45 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase131a hcase330a hcase330b hcase430b hcase411a hcase010b hcase021a hcase041a hcase111a hcase321a hcase401a hcase141a hcase441a hcase00 hcase03 hcase10 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase42
                      omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase430a hcase430b hcase411a hcase411b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase42 hcase44
        omega
  ·
    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut55 hcut4 hcut46 hcut52 hcut53 hcut8 hcut32 hcut26 hcut31 hcut48 hcut58 hcut15 hcut59 hcut36 hcut21 hcut35 hcut30 hcut40 hcut27 hcut13 hcut50 hcut16 hcut22 hcut33 hcut51 hcut0 hcut3 hcut23 hcut60 hcut42 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase001a hcase001b hcase131a hcase131b hcase330b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
    omega

#print axioms symbolic_mask127_integer_shard002
end Jsp404.SixExactFloorKernel
