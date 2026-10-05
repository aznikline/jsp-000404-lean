import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_mask222_integer_shard003 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut12 : (s01 + s43 + u01 + u43) + 1 ≤ (s33 + 2))
    (hcut3 : (s03 + u03) + 1 ≤ (s13 + 2))
    (hcut29 : (s03 + s04 + s11 + u03 + u04 + u11 + 1) + 1 ≤ (n))
    (hcut45 : (s02 + s42 + u02 + u42) + 1 ≤ (s12 + 2))
    (hcut40 : (s12 + s13 + s14 + s40 + s41 + u12 + u13 + u14 + u40 + u41) + 1 ≤ (n + 1))
    (hcut37 : (s03 + s04 + s12 + s41 + u03 + u04 + u12 + u41) + 1 ≤ (n))
    (hcut7 : (s03 + s04 + u03 + u04) + 1 ≤ (s13 + s14 + 4))
    (hcut24 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 1))
    (hcut11 : (s02 + s30 + s41 + s42 + u02 + u30 + u41 + u42 + 1) + 1 ≤ (n))
    (hcut39 : (s14 + s40 + u14 + u40) + 1 ≤ (n))
    (hcut8 : (s12 + s13 + s40 + s41 + u12 + u13 + u40 + u41) + 1 ≤ (n))
    (hcut57 : (s04 + s10 + s11 + s12 + u04 + u10 + u11 + u12) + 1 ≤ (n + 1))
    (hcut2 : (s00 + s33 + s44 + u00 + u33 + u44) + 1 ≤ (n + 2))
    (hcut4 : (s44 + u44) + 1 ≤ (s34 + 3))
    (hcut55 : (s10 + s11 + s13 + s14 + u10 + u11 + u13 + u14) + 1 ≤ (n))
    (hcut44 : (s00 + s43 + u00 + u43) + 1 ≤ (n + 1))
    (hcut46 : (s40 + u40 + 1) + 1 ≤ (n))
    (hcut47 : (s04 + s10 + u04 + u10) + 1 ≤ (n))
    (hcut51 : (s03 + s04 + s10 + u03 + u04 + u10) + 1 ≤ (n + 1))
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
    (hcase010a : s01 = 0)
    (hcase010b : u01 = 0)
    (hcase001a : 1 ≤ s00)
    (hcase001b : u00 = 1)
    (hcase121a : 1 ≤ s12)
    (hcase121b : u12 = 1)
    (hcase101a : 1 ≤ s10)
    (hcase101b : u10 = 1)
    : False := by
  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
  ·
    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
    ·
      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
      ·
        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
        ·
          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121b hcase101b hcase430b hcase130a hcase130b hcase030b hcase140a hcase140b hcase040b hcase410b hcase400b hcase420b hcase020b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase121b hcase101b hcase430b hcase130a hcase130b hcase030b hcase140a hcase140b hcase040b hcase410b hcase400b hcase420a hcase420b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                ·
                  clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase121b hcase101b hcase430b hcase130a hcase130b hcase030b hcase140a hcase140b hcase040b hcase410b hcase400b hcase421a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                  omega
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase001b hcase101a hcase101b hcase430b hcase130a hcase130b hcase030a hcase030b hcase140a hcase140b hcase040a hcase040b hcase410a hcase410b hcase401a hcase440b hcase420b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase001b hcase121a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030a hcase030b hcase140a hcase140b hcase040a hcase040b hcase410a hcase410b hcase401a hcase440b hcase421a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34
                    omega
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut12 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase121b hcase101a hcase101b hcase430a hcase430b hcase130a hcase130b hcase030b hcase140a hcase140b hcase040b hcase410a hcase410b hcase401a hcase401b hcase020b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030b hcase140a hcase140b hcase040b hcase410a hcase410b hcase401a hcase441a hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42
                    omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030b hcase140a hcase140b hcase040b hcase411a hcase420b hcase020b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase44
                  omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase121b hcase101a hcase101b hcase430b hcase130a hcase130b hcase030b hcase140a hcase140b hcase040b hcase411a hcase420a hcase420b hcase021a hcase400b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030b hcase140a hcase140b hcase040b hcase411a hcase420a hcase420b hcase021a hcase401a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase121b hcase101a hcase101b hcase430b hcase130a hcase130b hcase030b hcase140a hcase140b hcase040b hcase411a hcase421a hcase400b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030b hcase140a hcase140b hcase040b hcase411a hcase421a hcase401a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                  omega
          ·
            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut12 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase001b hcase121a hcase101a hcase430a hcase430b hcase130b hcase030a hcase030b hcase140b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
            omega
        ·
          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
          ·
            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030b hcase020b hcase420b hcase400a hcase400b hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut40 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030a hcase030b hcase141a hcase141b hcase020b hcase420b hcase400b hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                  omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030b hcase020b hcase420b hcase401a hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase430b hcase130a hcase130b hcase030b hcase141a hcase020b hcase420b hcase401a hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                  omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase121b hcase101b hcase430b hcase130a hcase130b hcase030b hcase141b hcase020a hcase020b hcase421a hcase400b hcase040b hcase410b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030b hcase020a hcase020b hcase421a hcase400a hcase400b hcase040b hcase411a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase430b hcase130a hcase130b hcase030b hcase141a hcase141b hcase020a hcase020b hcase421a hcase400b hcase041a hcase410b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030a hcase030b hcase141a hcase141b hcase020a hcase020b hcase421a hcase400b hcase041a hcase411a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030b hcase020a hcase020b hcase421a hcase401a hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                  omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase001b hcase121a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030a hcase030b hcase020a hcase020b hcase421a hcase401a hcase041a hcase041b hcase440b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase430b hcase130a hcase130b hcase030b hcase141a hcase020a hcase020b hcase421a hcase401a hcase041a hcase441a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41
                    omega
          ·
            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase001b hcase121a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030a hcase030b hcase440b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42
              omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030b hcase021a hcase441a hcase400a hcase400b hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030a hcase030b hcase141a hcase141b hcase021a hcase441a hcase400b hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                  omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase130a hcase130b hcase030b hcase021a hcase441a hcase401a hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                  omega
                ·
                  clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase430b hcase130a hcase130b hcase030b hcase141a hcase021a hcase441a hcase401a hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42
                  omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut12 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase001b hcase121a hcase121b hcase101a hcase101b hcase430a hcase430b hcase130b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase41 hcase42 hcase44
        omega
    ·
      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
      ·
        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
        ·
          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase121b hcase101b hcase430b hcase131b hcase030b hcase040b hcase400b hcase410b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase030b hcase040b hcase400a hcase400b hcase411a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
              omega
          ·
            clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase030b hcase040b hcase401a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase44
            omega
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase430b hcase131a hcase131b hcase030b hcase041a hcase140a hcase140b hcase400b hcase410b hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase430b hcase131a hcase131b hcase030b hcase041a hcase140a hcase140b hcase400b hcase410b hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase430b hcase131a hcase131b hcase030b hcase041a hcase140a hcase140b hcase400b hcase410b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                  omega
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut40 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase101b hcase430b hcase131a hcase131b hcase030a hcase030b hcase041a hcase140a hcase140b hcase400b hcase411a hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase131b hcase030a hcase030b hcase041a hcase140a hcase140b hcase400b hcase411a hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase131b hcase030a hcase030b hcase041a hcase140a hcase140b hcase400b hcase411a hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                  omega
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut11 hcut39 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase430b hcase131a hcase030b hcase041a hcase140b hcase401a hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase430b hcase131a hcase030b hcase041a hcase140b hcase401a hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                  omega
              ·
                clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase430b hcase131a hcase030b hcase041a hcase140b hcase401a hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase44
                omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase430b hcase131a hcase131b hcase030b hcase041a hcase141a hcase141b hcase400b hcase410b hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase430b hcase131a hcase131b hcase030b hcase041a hcase141a hcase141b hcase400b hcase410b hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase430b hcase131a hcase131b hcase030b hcase041a hcase141a hcase141b hcase400b hcase410b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                  omega
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase430b hcase131a hcase030b hcase041a hcase141a hcase400a hcase400b hcase411a hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase430b hcase131a hcase030b hcase041a hcase141a hcase400a hcase400b hcase411a hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                ·
                  clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase430b hcase131a hcase030b hcase041a hcase141a hcase400a hcase400b hcase411a hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                  omega
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase430b hcase131a hcase030b hcase041a hcase141a hcase401a hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                  omega
                ·
                  clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase430b hcase131a hcase030b hcase041a hcase141a hcase401a hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase44
                  omega
              ·
                clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut7 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase430b hcase131a hcase030b hcase041a hcase141a hcase401a hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase41 hcase42 hcase44
                omega
      ·
        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
        ·
          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase001b hcase121a hcase101a hcase101b hcase430b hcase031a hcase031b hcase410a hcase410b hcase440b hcase00 hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase42
            omega
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                clear hn4 hsum_nat3 hcut12 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase121b hcase101b hcase430b hcase131a hcase131b hcase031a hcase410b hcase441a hcase400b hcase040b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase131b hcase031a hcase410a hcase410b hcase441a hcase400b hcase041a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42
                omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut29 hcut45 hcut40 hcut37 hcut7 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase101b hcase430b hcase131a hcase031a hcase410a hcase410b hcase441a hcase401a hcase420b hcase020b hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut37 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase101b hcase430b hcase131a hcase031a hcase410a hcase410b hcase441a hcase401a hcase420b hcase020b hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34
                    omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase031a hcase410a hcase410b hcase441a hcase401a hcase420a hcase420b hcase021a hcase140a hcase140b hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase031a hcase410a hcase410b hcase441a hcase401a hcase420a hcase420b hcase021a hcase140b hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34
                      omega
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut29 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase031a hcase410a hcase410b hcase441a hcase401a hcase420a hcase420b hcase021a hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase031a hcase410a hcase410b hcase441a hcase401a hcase420a hcase420b hcase021a hcase141a hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34
                      omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut29 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase031a hcase410a hcase410b hcase441a hcase401a hcase421a hcase040b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase33 hcase34
                  omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase031a hcase410a hcase410b hcase441a hcase401a hcase421a hcase041a hcase140b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase031a hcase410a hcase410b hcase441a hcase401a hcase421a hcase041a hcase141a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34
                    omega
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut40 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase101b hcase430b hcase131a hcase131b hcase031a hcase411a hcase140a hcase140b hcase400b hcase020b hcase420b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase131b hcase031a hcase411a hcase140a hcase140b hcase400b hcase020a hcase020b hcase421a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                  omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase131b hcase031a hcase411a hcase140a hcase140b hcase400b hcase021a hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                omega
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut29 hcut40 hcut37 hcut7 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase031a hcase411a hcase140a hcase140b hcase401a hcase040b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                omega
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut40 hcut37 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase101b hcase430b hcase131a hcase031a hcase411a hcase140b hcase401a hcase041a hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase031a hcase411a hcase140b hcase401a hcase041a hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase031a hcase411a hcase140b hcase401a hcase041a hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                  omega
          ·
            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut29 hcut45 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase101b hcase430b hcase131a hcase031a hcase411a hcase020b hcase420b hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut37 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase101b hcase430b hcase131a hcase031a hcase411a hcase141a hcase020b hcase420b hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase44
                  omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase131b hcase031a hcase411a hcase141a hcase141b hcase020a hcase020b hcase421a hcase400b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                  omega
                ·
                  rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut29 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase031a hcase411a hcase020a hcase020b hcase421a hcase401a hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase031a hcase411a hcase141a hcase020a hcase020b hcase421a hcase401a hcase041a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase44
                    omega
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut29 hcut37 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase031a hcase411a hcase021a hcase040b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase40 hcase42 hcase44
                omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut7 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase131b hcase031a hcase411a hcase141a hcase141b hcase021a hcase041a hcase400b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase430b hcase131a hcase031a hcase411a hcase141a hcase021a hcase041a hcase401a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase33 hcase34 hcase42 hcase44
                  omega
  ·
    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase001b hcase121a hcase121b hcase101a hcase101b hcase330b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase44
      omega
    ·
      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
      ·
        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
        ·
          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
          ·
            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase121b hcase101b hcase431a hcase331a hcase331b hcase040b hcase030b hcase410b hcase440b hcase400b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42
                omega
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut12 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase121b hcase101a hcase101b hcase331a hcase331b hcase040b hcase030b hcase410a hcase410b hcase440a hcase440b hcase401a hcase401b hcase020b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase331b hcase040b hcase030b hcase410a hcase410b hcase440b hcase401a hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42
                  omega
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase121b hcase101a hcase101b hcase331a hcase040b hcase030b hcase410a hcase410b hcase020b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase42
                omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat3 hcut3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase121b hcase101b hcase431a hcase331a hcase040b hcase030b hcase410b hcase441a hcase021a hcase400b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase040b hcase030b hcase410a hcase410b hcase441a hcase021a hcase401a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42
                  omega
          ·
            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut12 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase121b hcase101a hcase101b hcase331a hcase331b hcase040b hcase030b hcase411a hcase411b hcase020b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase42 hcase44
              omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut39 hcut8 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase121b hcase101a hcase101b hcase431a hcase331a hcase040b hcase030b hcase411a hcase021a hcase400b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase040b hcase030b hcase411a hcase021a hcase401a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase44
                omega
        ·
          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut12 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase001b hcase121a hcase121b hcase101a hcase101b hcase431a hcase431b hcase331a hcase331b hcase040a hcase040b hcase020a hcase020b hcase130b hcase00 hcase01 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase44
              omega
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase101a hcase101b hcase431a hcase331a hcase040b hcase031a hcase020b hcase131a hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase44
                omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase121b hcase101b hcase431a hcase331a hcase040b hcase031a hcase020a hcase020b hcase131a hcase131b hcase421a hcase410b hcase400b hcase00 hcase01 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase040b hcase031a hcase020a hcase020b hcase131a hcase421a hcase410a hcase410b hcase401a hcase00 hcase01 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                    omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase040b hcase031a hcase020a hcase020b hcase131a hcase421a hcase411a hcase00 hcase01 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase44
                  omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut12 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase001b hcase121a hcase121b hcase101a hcase101b hcase431a hcase431b hcase331a hcase331b hcase040a hcase040b hcase021a hcase021b hcase130b hcase00 hcase01 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase40 hcase41 hcase42 hcase44
              omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  clear hn4 hsum_nat3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase121b hcase101b hcase431a hcase331a hcase040b hcase031a hcase021a hcase131a hcase131b hcase400b hcase410b hcase00 hcase01 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase040b hcase031a hcase021a hcase131a hcase400a hcase400b hcase411a hcase00 hcase01 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase44
                  omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase040b hcase031a hcase021a hcase131a hcase401a hcase00 hcase01 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase44
                omega
      ·
        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
        ·
          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase431a hcase331a hcase041a hcase400b hcase030b hcase410b hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase431a hcase331a hcase041a hcase400b hcase030b hcase410b hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                  omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase431a hcase331a hcase041a hcase400b hcase030b hcase410b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase44
                omega
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut45 hcut40 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase101a hcase101b hcase431a hcase331a hcase041a hcase400b hcase030a hcase030b hcase411a hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                  omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut40 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase041a hcase400b hcase030a hcase030b hcase411a hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase44
                  omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut40 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase041a hcase400b hcase030a hcase030b hcase411a hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase42 hcase44
                omega
          ·
            rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
            ·
              rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut45 hcut40 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase101a hcase101b hcase431a hcase331a hcase041a hcase400b hcase031a hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut40 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase041a hcase400b hcase031a hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase44
                omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut40 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase041a hcase400b hcase031a hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42 hcase44
              omega
        ·
          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut12 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase001b hcase121a hcase101a hcase431a hcase431b hcase331a hcase331b hcase401a hcase401b hcase440a hcase440b hcase030a hcase030b hcase140b hcase130b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42
                  omega
                ·
                  clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut2 hcut4 hcut55 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase431a hcase331a hcase331b hcase041a hcase401a hcase440b hcase030b hcase140b hcase131a hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42
                  omega
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase431a hcase331a hcase331b hcase041a hcase401a hcase440b hcase030b hcase141a hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase41
                    omega
                  ·
                    clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase431a hcase331a hcase331b hcase041a hcase401a hcase440b hcase030b hcase141a hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase41
                    omega
                ·
                  clear hn4 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase431a hcase331a hcase331b hcase041a hcase401a hcase440b hcase030b hcase141a hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42
                  omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut12 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase001b hcase121a hcase121b hcase101a hcase101b hcase431a hcase431b hcase331a hcase331b hcase041a hcase041b hcase401a hcase401b hcase440a hcase440b hcase130b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42
                omega
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut45 hcut37 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase101a hcase101b hcase431a hcase331a hcase331b hcase041a hcase401a hcase440b hcase031a hcase131a hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase32 hcase34 hcase41
                    omega
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut24 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase331b hcase041a hcase401a hcase440b hcase031a hcase131a hcase020a hcase020b hcase421a hcase140b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase331b hcase041a hcase401a hcase440b hcase031a hcase131a hcase020a hcase020b hcase421a hcase141a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                      omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut40 hcut37 hcut24 hcut11 hcut39 hcut57 hcut2 hcut4 hcut55 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase331b hcase041a hcase401a hcase440b hcase031a hcase131a hcase021a hcase140b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut12 hcut3 hcut29 hcut37 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase331b hcase041a hcase401a hcase440b hcase031a hcase131a hcase021a hcase141a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42
                    omega
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut12 hcut3 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase001b hcase121a hcase101a hcase431a hcase431b hcase331a hcase331b hcase401a hcase401b hcase441a hcase441b hcase140b hcase130b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42
                omega
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut45 hcut40 hcut37 hcut24 hcut11 hcut39 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase101a hcase101b hcase431a hcase331a hcase041a hcase401a hcase441a hcase140b hcase131a hcase020b hcase420b hcase00 hcase01 hcase03 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                    omega
                  ·
                    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                    ·
                      clear hn4 hsum_nat3 hcut3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase431a hcase331a hcase041a hcase401a hcase441a hcase140b hcase131a hcase020a hcase020b hcase421a hcase030b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut40 hcut37 hcut24 hcut11 hcut39 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase041a hcase401a hcase441a hcase140b hcase131a hcase020a hcase020b hcase421a hcase031a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                      omega
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    clear hn4 hsum_nat3 hcut3 hcut29 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase431a hcase331a hcase041a hcase401a hcase441a hcase140b hcase131a hcase021a hcase030b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut40 hcut37 hcut24 hcut11 hcut39 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase041a hcase401a hcase441a hcase140b hcase131a hcase021a hcase031a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42
                    omega
            ·
              rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat3 hcut3 hcut29 hcut45 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase101a hcase431a hcase331a hcase041a hcase401a hcase441a hcase141a hcase130a hcase130b hcase030b hcase020b hcase420b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut3 hcut29 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase431a hcase331a hcase041a hcase401a hcase441a hcase141a hcase130a hcase130b hcase030b hcase020a hcase020b hcase421a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                      omega
                  ·
                    clear hn4 hsum_nat3 hcut3 hcut29 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase431a hcase331a hcase041a hcase401a hcase441a hcase141a hcase130a hcase130b hcase030b hcase021a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut12 hcut29 hcut45 hcut40 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut57 hcut2 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase001b hcase121a hcase121b hcase101a hcase101b hcase431a hcase431b hcase331a hcase331b hcase041a hcase041b hcase401a hcase401b hcase441a hcase441b hcase141a hcase141b hcase130b hcase00 hcase01 hcase02 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42
                  omega
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut45 hcut37 hcut24 hcut11 hcut39 hcut8 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase101a hcase101b hcase431a hcase331a hcase041a hcase401a hcase441a hcase141a hcase131a hcase020b hcase420b hcase00 hcase01 hcase03 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                    omega
                  ·
                    rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                    ·
                      clear hn4 hsum_nat3 hcut3 hcut29 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase431a hcase331a hcase041a hcase401a hcase441a hcase141a hcase131a hcase020a hcase020b hcase421a hcase030b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut37 hcut24 hcut11 hcut39 hcut8 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase041a hcase401a hcase441a hcase141a hcase131a hcase020a hcase020b hcase421a hcase031a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41
                      omega
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    clear hn4 hsum_nat3 hcut3 hcut29 hcut37 hcut7 hcut24 hcut11 hcut39 hcut8 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase431a hcase331a hcase041a hcase401a hcase441a hcase141a hcase131a hcase021a hcase030b hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut3 hcut29 hcut37 hcut24 hcut11 hcut39 hcut8 hcut57 hcut4 hcut55 hcut44 hcut46 hcut47 hcut51 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase010a hcase010b hcase001a hcase121a hcase101a hcase101b hcase431a hcase331a hcase041a hcase401a hcase441a hcase141a hcase131a hcase021a hcase031a hcase00 hcase01 hcase10 hcase11 hcase12 hcase30 hcase31 hcase32 hcase34 hcase41 hcase42
                    omega

#print axioms symbolic_mask222_integer_shard003
end Jsp404.SixExactFloorKernel
