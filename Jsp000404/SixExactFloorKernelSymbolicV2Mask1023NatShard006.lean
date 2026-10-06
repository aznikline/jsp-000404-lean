import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_v2_mask1023_integer_shard006 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut66 : (s11 + s12 + s14 + u11 + u12 + u14 + 1) + 1 ≤ (n))
    (hcut101 : (s10 + s13 + s14 + s31 + s40 + s44 + u10 + u13 + u14 + u31 + u40 + u44) + 1 ≤ (2 * n + 1))
    (hcut1 : (s30 + s34 + s41 + s42 + s43 + u30 + u34 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut97 : (s12 + s14 + s30 + s31 + s32 + u12 + u14 + u30 + u31 + u32) + 1 ≤ (n))
    (hcut100 : (s00 + s04 + s13 + s40 + s44 + u00 + u04 + u13 + u40 + u44) + 1 ≤ (2 * n))
    (hcut5 : (s04 + u04) + 1 ≤ (s14 + 2))
    (hcut12 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 2))
    (hcut60 : (s03 + u03) + 1 ≤ (s13 + 2))
    (hcut7 : (s42 + u42) + 1 ≤ (s10 + 1))
    (hcut0 : (s02 + s03 + s10 + s11 + s14 + s33 + u02 + u03 + u10 + u11 + u14 + u33) + 1 ≤ (n + 1))
    (hcut50 : (s13 + s14 + u13 + u14 + 2) + 1 ≤ (n))
    (hcut76 : (s12 + s13 + s14 + s31 + s40 + u12 + u13 + u14 + u31 + u40) + 1 ≤ (n + 2))
    (hcut94 : (s12 + s13 + s14 + s31 + s32 + u12 + u13 + u14 + u31 + u32) + 1 ≤ (n))
    (hcut78 : (s13 + s30 + u13 + u30 + 2) + 1 ≤ (n))
    (hcut95 : (s10 + s11 + s12 + s13 + u10 + u11 + u12 + u13) + 1 ≤ (n))
    (hcut85 : (s00 + s04 + s11 + s12 + s13 + s41 + s44 + u00 + u04 + u11 + u12 + u13 + u41 + u44) + 1 ≤ (2 * n + 2))
    (hcut62 : (s04 + s32 + u04 + u32 + 2) + 1 ≤ (n))
    (hcut38 : (s10 + s43 + s44 + u10 + u43 + u44) + 1 ≤ (n + 2))
    (hcut41 : (s11 + s12 + s13 + u11 + u12 + u13 + 1) + 1 ≤ (n))
    (hcut77 : (s41 + u41) + 1 ≤ (s31 + 2))
    (hcut79 : (s01 + s30 + s34 + s41 + u01 + u30 + u34 + u41) + 1 ≤ (n + 1))
    (hcut30 : (s11 + s41 + u11 + u41 + 2) + 1 ≤ (n))
    (hcut14 : (s10 + s43 + u10 + u43) + 1 ≤ (n + 1))
    (hcut68 : (s02 + s10 + u02 + u10) + 1 ≤ (n))
    (hcut4 : (s31 + s32 + s40 + s43 + s44 + u31 + u32 + u40 + u43 + u44) + 1 ≤ (n + s11 + 3))
    (hcut8 : (s12 + s13 + s14 + s30 + s32 + s41 + u12 + u13 + u14 + u30 + u32 + u41) + 1 ≤ (n + 1))
    (hcut99 : (s30 + s41 + s42 + u30 + u41 + u42) + 1 ≤ (s10 + 2))
    (hcut11 : (s02 + s03 + u02 + u03) + 1 ≤ (s34 + 1))
    (hcut86 : (s13 + s14 + s31 + u13 + u14 + u31 + 1) + 1 ≤ (n))
    (hcut43 : (s01 + s10 + u01 + u10) + 1 ≤ (n))
    (hcut6 : (s40 + u40) + 1 ≤ (s30 + 2))
    (hcut21 : (s11 + s30 + u11 + u30 + 1) + 1 ≤ (n))
    (hcut96 : (s12 + s30 + u12 + u30 + 2) + 1 ≤ (n))
    (hcut55 : (s33 + s41 + s42 + u33 + u41 + u42 + 1) + 1 ≤ (n))
    (hcut84 : (s00 + s01 + s04 + s11 + s13 + s34 + s41 + u00 + u01 + u04 + u11 + u13 + u34 + u41) + 1 ≤ (2 * n + 1))
    (hcut31 : (s01 + s34 + u01 + u34) + 1 ≤ (s44 + 2))
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
    (hcase001a : 1 ≤ s00)
    (hcase001b : u00 = 1)
    (hcase301a : 1 ≤ s30)
    (hcase301b : u30 = 1)
    (hcase120a : s12 = 0)
    (hcase120b : u12 = 0)
    (hcase311a : 1 ≤ s31)
    (hcase311b : u31 = 1)
    : False := by
  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
  ·
    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
    ·
      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
      ·
        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301b hcase120a hcase120b hcase311b hcase330a hcase330b hcase340a hcase340b hcase040b hcase110a hcase110b hcase130a hcase130b hcase010b hcase430b hcase410b hcase400b hcase420b hcase00 hcase02 hcase03 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340b hcase040b hcase110a hcase110b hcase130a hcase130b hcase010b hcase430b hcase410a hcase410b hcase400b hcase421a hcase00 hcase02 hcase03 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase44
                      omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase110a hcase110b hcase130a hcase130b hcase010a hcase010b hcase430b hcase410a hcase410b hcase401a hcase440b hcase00 hcase02 hcase03 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase42
                      omega
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase301b hcase120a hcase120b hcase311b hcase330a hcase330b hcase340a hcase340b hcase040b hcase110a hcase110b hcase130a hcase130b hcase010b hcase430b hcase410b hcase401a hcase441a hcase420b hcase00 hcase02 hcase03 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase110a hcase110b hcase130a hcase130b hcase010a hcase010b hcase430a hcase430b hcase410a hcase410b hcase401a hcase441a hcase441b hcase421a hcase00 hcase02 hcase03 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32
                        omega
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340b hcase040b hcase110a hcase110b hcase130a hcase130b hcase010b hcase430b hcase411a hcase400b hcase00 hcase02 hcase03 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase110a hcase110b hcase130a hcase130b hcase010a hcase010b hcase430a hcase430b hcase411a hcase401a hcase00 hcase02 hcase03 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase42 hcase44
                    omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase110b hcase130b hcase010a hcase010b hcase431a hcase431b hcase400a hcase400b hcase100b hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase41 hcase42 hcase44
                    omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hcut66 hcut101 hcut1 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase110b hcase130b hcase010a hcase010b hcase431a hcase400b hcase101a hcase420b hcase410b hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase110a hcase110b hcase130a hcase130b hcase010a hcase010b hcase431a hcase400a hcase400b hcase101a hcase101b hcase420a hcase420b hcase411a hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase110a hcase110b hcase130a hcase130b hcase010a hcase010b hcase431a hcase400a hcase400b hcase101a hcase101b hcase421a hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase41 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase110a hcase110b hcase130a hcase130b hcase010a hcase010b hcase431a hcase401a hcase00 hcase02 hcase03 hcase10 hcase12 hcase14 hcase30 hcase31 hcase32 hcase41 hcase42 hcase44
                  omega
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase110b hcase130b hcase011a hcase011b hcase100b hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat4 hcut66 hcut101 hcut1 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase330b hcase340b hcase040a hcase040b hcase110b hcase130b hcase101a hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    clear hn4 hsum_nat0 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120b hcase311a hcase330b hcase340b hcase040a hcase040b hcase110b hcase320b hcase400b hcase420b hcase410b hcase00 hcase01 hcase02 hcase03 hcase10 hcase12 hcase14 hcase30 hcase31 hcase43 hcase44
                    omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120b hcase311a hcase330b hcase340b hcase040a hcase040b hcase110b hcase320b hcase400a hcase400b hcase420a hcase420b hcase411a hcase411b hcase100b hcase00 hcase01 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase330b hcase340b hcase040a hcase040b hcase110a hcase110b hcase320b hcase400b hcase420a hcase420b hcase411a hcase101a hcase00 hcase01 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase43 hcase44
                      omega
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120b hcase311a hcase330b hcase340b hcase040a hcase040b hcase110b hcase320b hcase400a hcase400b hcase421a hcase421b hcase100b hcase00 hcase01 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase41 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase330b hcase340b hcase040a hcase040b hcase110a hcase110b hcase320b hcase400b hcase421a hcase101a hcase00 hcase01 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase41 hcase43 hcase44
                    omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120b hcase311a hcase330b hcase340b hcase040a hcase040b hcase110b hcase320b hcase401a hcase401b hcase430a hcase430b hcase100b hcase00 hcase01 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase41 hcase42 hcase44
                    omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat0 hcut66 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120b hcase311a hcase330b hcase340b hcase040a hcase040b hcase110b hcase320b hcase401a hcase430b hcase101a hcase410b hcase420b hcase00 hcase01 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase320a hcase320b hcase401a hcase430a hcase430b hcase101a hcase101b hcase410a hcase410b hcase421a hcase00 hcase01 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase320a hcase320b hcase401a hcase430a hcase430b hcase101a hcase101b hcase411a hcase00 hcase01 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase42 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase320a hcase320b hcase401a hcase431a hcase00 hcase01 hcase02 hcase03 hcase10 hcase12 hcase14 hcase30 hcase31 hcase41 hcase42 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut66 hcut101 hcut1 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase330b hcase340b hcase040a hcase040b hcase110a hcase110b hcase131a hcase131b hcase321a hcase00 hcase01 hcase02 hcase03 hcase10 hcase12 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase111a hcase111b hcase100b hcase00 hcase01 hcase02 hcase03 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut86 hcut43 hcut6 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340b hcase040b hcase101a hcase101b hcase130a hcase130b hcase400b hcase420b hcase410b hcase430b hcase010b hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase44
                        omega
                      ·
                        clear hn4 hcut66 hcut101 hcut1 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut86 hcut6 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase330b hcase340b hcase040b hcase111a hcase101a hcase130b hcase400b hcase420b hcase410b hcase430b hcase011a hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hcut66 hcut101 hcut1 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase311a hcase330b hcase340b hcase040a hcase040b hcase111a hcase101a hcase130b hcase400b hcase420b hcase410b hcase431a hcase00 hcase01 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase44
                      omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut14 hcut68 hcut4 hcut8 hcut99 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340b hcase040b hcase101a hcase101b hcase130a hcase130b hcase400b hcase420b hcase411a hcase430b hcase010b hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut86 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340b hcase040b hcase111a hcase111b hcase101a hcase130a hcase130b hcase400b hcase420a hcase420b hcase411a hcase430b hcase011a hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase111a hcase111b hcase101a hcase101b hcase130a hcase130b hcase400a hcase400b hcase420a hcase420b hcase411a hcase431a hcase00 hcase01 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase44
                      omega
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                    ·
                      clear hn4 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340b hcase040b hcase111b hcase101a hcase101b hcase130a hcase130b hcase400b hcase421a hcase430b hcase010b hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase41 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut86 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340b hcase040b hcase111a hcase111b hcase101a hcase130a hcase130b hcase400b hcase421a hcase430b hcase011a hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase41 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase111a hcase111b hcase101a hcase101b hcase130a hcase130b hcase400a hcase400b hcase421a hcase431a hcase00 hcase01 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase41 hcase44
                    omega
              ·
                rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                ·
                  rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut86 hcut43 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340b hcase040b hcase101a hcase101b hcase130a hcase130b hcase401a hcase430b hcase010b hcase410b hcase420b hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase111a hcase111b hcase101a hcase101b hcase130a hcase130b hcase401a hcase430a hcase430b hcase010a hcase010b hcase410a hcase410b hcase421a hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase111a hcase111b hcase101a hcase101b hcase130a hcase130b hcase401a hcase430a hcase430b hcase010a hcase010b hcase411a hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase42 hcase44
                      omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase111b hcase101a hcase101b hcase130a hcase130b hcase401a hcase430b hcase011a hcase011b hcase420a hcase420b hcase440b hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase41
                        omega
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          clear hn4 hcut66 hcut101 hcut1 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut86 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase120a hcase120b hcase311a hcase330b hcase340b hcase040b hcase111a hcase101a hcase130b hcase401a hcase430b hcase011a hcase420b hcase441a hcase410b hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase111a hcase111b hcase101a hcase101b hcase130a hcase130b hcase401a hcase430a hcase430b hcase011a hcase011b hcase420a hcase420b hcase441a hcase441b hcase411a hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase111a hcase111b hcase101a hcase101b hcase130a hcase130b hcase401a hcase430a hcase430b hcase011a hcase011b hcase421a hcase00 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase41 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase340a hcase340b hcase040a hcase040b hcase111a hcase111b hcase101a hcase101b hcase130a hcase130b hcase401a hcase431a hcase00 hcase01 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase41 hcase42 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat4 hcut66 hcut101 hcut1 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase330b hcase340b hcase040a hcase040b hcase111a hcase101a hcase131a hcase00 hcase01 hcase02 hcase03 hcase12 hcase14 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut66 hcut101 hcut1 hcut100 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase330b hcase340b hcase00 hcase01 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
    ·
      rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
      ·
        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
        ·
          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase020a hcase020b hcase140b hcase040a hcase040b hcase110b hcase400a hcase400b hcase410a hcase410b hcase420a hcase420b hcase100b hcase00 hcase12 hcase13 hcase30 hcase31 hcase32 hcase43 hcase44
                          omega
                        ·
                          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                          ·
                            clear hn4 hsum_nat0 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301b hcase120b hcase311b hcase330a hcase330b hcase341b hcase010a hcase010b hcase030a hcase030b hcase020a hcase020b hcase140b hcase040a hcase040b hcase110b hcase400b hcase410b hcase420b hcase101a hcase130b hcase00 hcase12 hcase30 hcase31 hcase32 hcase43 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase020a hcase020b hcase140b hcase040a hcase040b hcase110b hcase400b hcase410b hcase420b hcase101a hcase131a hcase00 hcase12 hcase30 hcase31 hcase32 hcase43 hcase44
                            omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase010b hcase030b hcase020b hcase140a hcase140b hcase040b hcase110a hcase110b hcase400b hcase410a hcase410b hcase421a hcase00 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase43 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase010b hcase030b hcase020b hcase140a hcase140b hcase040b hcase110a hcase110b hcase400b hcase411a hcase00 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          clear hn4 hsum_nat1 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase301b hcase120a hcase120b hcase311b hcase330a hcase330b hcase341b hcase010b hcase030b hcase020b hcase140a hcase140b hcase040b hcase110a hcase110b hcase401a hcase430b hcase410b hcase420b hcase00 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase020a hcase020b hcase140a hcase140b hcase040a hcase040b hcase110a hcase110b hcase401a hcase430a hcase430b hcase410a hcase410b hcase421a hcase00 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase020a hcase020b hcase140a hcase140b hcase040a hcase040b hcase110a hcase110b hcase401a hcase430a hcase430b hcase411a hcase00 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase42 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase020a hcase020b hcase140a hcase140b hcase040a hcase040b hcase110a hcase110b hcase401a hcase431a hcase00 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase41 hcase42 hcase44
                      omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase010a hcase010b hcase030a hcase030b hcase020a hcase020b hcase140a hcase140b hcase040a hcase040b hcase111a hcase111b hcase440b hcase00 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43
                    omega
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase010b hcase030b hcase020b hcase140a hcase140b hcase040b hcase111a hcase111b hcase441a hcase400b hcase00 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase41 hcase42 hcase43
                      omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010b hcase030b hcase020b hcase140a hcase140b hcase040b hcase111b hcase441a hcase401a hcase430b hcase00 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase41 hcase42
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase020a hcase020b hcase140a hcase140b hcase040a hcase040b hcase111a hcase111b hcase441a hcase441b hcase401a hcase431a hcase00 hcase10 hcase12 hcase13 hcase30 hcase31 hcase32 hcase41 hcase42
                        omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase020a hcase020b hcase140b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  clear hn4 hsum_nat1 hcut66 hcut101 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase330b hcase341a hcase010b hcase030b hcase020b hcase400b hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut100 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase330a hcase330b hcase341a hcase341b hcase010b hcase030b hcase020b hcase141a hcase400b hcase041a hcase420b hcase430b hcase410b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010b hcase030b hcase020b hcase141a hcase141b hcase400b hcase041a hcase420a hcase420b hcase430b hcase411a hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat1 hcut66 hcut101 hcut100 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase330b hcase341a hcase010b hcase030b hcase020b hcase141a hcase400b hcase041a hcase420a hcase420b hcase431a hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase41 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat1 hcut66 hcut101 hcut100 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase330b hcase341a hcase010b hcase030b hcase020b hcase141a hcase400b hcase041a hcase421a hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase41 hcase43 hcase44
                    omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        clear hn4 hsum_nat1 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase301b hcase120a hcase120b hcase311b hcase330a hcase330b hcase341b hcase010b hcase030b hcase020b hcase141a hcase141b hcase401a hcase410b hcase420b hcase430b hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut100 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase120a hcase120b hcase330a hcase330b hcase341a hcase341b hcase010b hcase030b hcase020b hcase141a hcase401a hcase410b hcase420b hcase430b hcase041a hcase00 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase020a hcase020b hcase141a hcase141b hcase401a hcase410a hcase410b hcase420a hcase420b hcase431a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase020a hcase020b hcase141a hcase141b hcase401a hcase410a hcase410b hcase421a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase020a hcase020b hcase141a hcase141b hcase401a hcase411a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase42 hcase43 hcase44
                  omega
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase021a hcase021b hcase100b hcase00 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase101a hcase110b hcase130b hcase140b hcase00 hcase04 hcase12 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase101a hcase110a hcase110b hcase130b hcase141a hcase00 hcase04 hcase12 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase010a hcase010b hcase030a hcase030b hcase101a hcase101b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase440b hcase00 hcase04 hcase12 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43
                      omega
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase010b hcase030a hcase030b hcase021a hcase101a hcase101b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase441a hcase400b hcase040b hcase00 hcase12 hcase30 hcase31 hcase32 hcase41 hcase42 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase021a hcase101a hcase101b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase441a hcase441b hcase400a hcase400b hcase041a hcase00 hcase12 hcase30 hcase31 hcase32 hcase41 hcase42 hcase43
                          omega
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase021a hcase021b hcase101a hcase110b hcase131a hcase140b hcase441a hcase401a hcase420b hcase410b hcase00 hcase04 hcase12 hcase30 hcase31 hcase32 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase021a hcase021b hcase101a hcase101b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase441a hcase441b hcase401a hcase420a hcase420b hcase411a hcase00 hcase04 hcase12 hcase30 hcase31 hcase32 hcase43
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase021a hcase021b hcase101a hcase101b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase441a hcase441b hcase401a hcase421a hcase00 hcase04 hcase12 hcase30 hcase31 hcase32 hcase41 hcase43
                          omega
                  ·
                    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
                    ·
                      rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hcut66 hcut101 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase330b hcase341a hcase010a hcase010b hcase030a hcase030b hcase021a hcase021b hcase101a hcase101b hcase110a hcase110b hcase131a hcase131b hcase320a hcase320b hcase440b hcase00 hcase04 hcase12 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43
                        omega
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                          ·
                            clear hn4 hcut66 hcut101 hcut97 hcut100 hcut5 hcut60 hcut7 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase120b hcase311a hcase330a hcase330b hcase341a hcase010b hcase030a hcase030b hcase021a hcase101a hcase110a hcase110b hcase131a hcase320b hcase441a hcase040b hcase400b hcase00 hcase12 hcase30 hcase31 hcase41 hcase42 hcase43
                            omega
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                              ·
                                clear hn4 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut99 hcut11 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010b hcase030a hcase030b hcase021a hcase101a hcase110a hcase110b hcase131a hcase320a hcase320b hcase441a hcase040b hcase401a hcase420b hcase430b hcase00 hcase12 hcase30 hcase31 hcase41
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase021a hcase021b hcase101a hcase101b hcase110a hcase110b hcase131a hcase131b hcase141a hcase141b hcase320a hcase320b hcase441a hcase441b hcase040a hcase040b hcase401a hcase420a hcase420b hcase431a hcase00 hcase12 hcase30 hcase31 hcase41
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase021a hcase021b hcase101a hcase101b hcase110a hcase110b hcase131a hcase131b hcase141a hcase141b hcase320a hcase320b hcase441a hcase441b hcase040a hcase040b hcase401a hcase421a hcase00 hcase12 hcase30 hcase31 hcase41 hcase43
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase021a hcase101a hcase101b hcase110a hcase110b hcase131a hcase131b hcase141a hcase141b hcase320a hcase320b hcase441a hcase441b hcase041a hcase00 hcase12 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase330a hcase330b hcase341a hcase010a hcase010b hcase030a hcase030b hcase021a hcase021b hcase101a hcase101b hcase110a hcase110b hcase131a hcase131b hcase141a hcase141b hcase321a hcase00 hcase04 hcase12 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                      omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase101a hcase111a hcase130b hcase00 hcase04 hcase12 hcase14 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase021a hcase021b hcase101a hcase111a hcase131a hcase140b hcase00 hcase04 hcase12 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase030a hcase030b hcase021a hcase021b hcase101a hcase111a hcase131a hcase141a hcase00 hcase04 hcase12 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
                    omega
        ·
          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase031a hcase031b hcase100b hcase00 hcase02 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
            ·
              rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      clear hn4 hsum_nat1 hcut66 hcut101 hcut1 hcut97 hcut100 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301b hcase120a hcase120b hcase311b hcase330a hcase330b hcase341a hcase341b hcase010b hcase031a hcase101a hcase101b hcase410b hcase430b hcase400b hcase140b hcase420b hcase00 hcase02 hcase04 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase44
                      omega
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase010b hcase031a hcase101a hcase101b hcase410a hcase410b hcase430a hcase430b hcase400b hcase140a hcase140b hcase421a hcase040b hcase00 hcase02 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase031a hcase101a hcase101b hcase410a hcase410b hcase430a hcase430b hcase400a hcase400b hcase140a hcase140b hcase421a hcase421b hcase041a hcase00 hcase02 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase44
                        omega
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010b hcase031a hcase101a hcase410a hcase410b hcase430b hcase400b hcase040b hcase00 hcase02 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase42 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase031a hcase101a hcase101b hcase410a hcase410b hcase430a hcase430b hcase400a hcase400b hcase141a hcase141b hcase041a hcase00 hcase02 hcase11 hcase12 hcase13 hcase30 hcase31 hcase32 hcase42 hcase44
                      omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      clear hn4 hsum_nat1 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase301b hcase120a hcase120b hcase311b hcase330a hcase330b hcase341a hcase341b hcase010b hcase031a hcase101a hcase101b hcase410b hcase430b hcase401a hcase420b hcase040b hcase00 hcase02 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase031a hcase101a hcase101b hcase410a hcase410b hcase430a hcase430b hcase401a hcase401b hcase420a hcase420b hcase041a hcase00 hcase02 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase031a hcase031b hcase101a hcase101b hcase410a hcase410b hcase430a hcase430b hcase401a hcase421a hcase00 hcase02 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase44
                    omega
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase010b hcase031a hcase101a hcase101b hcase410a hcase410b hcase431a hcase040b hcase400b hcase00 hcase02 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase42 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase031a hcase031b hcase101a hcase101b hcase410a hcase410b hcase431a hcase040a hcase040b hcase401a hcase00 hcase02 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase42 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase031a hcase101a hcase101b hcase410a hcase410b hcase431a hcase431b hcase041a hcase00 hcase02 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase40 hcase42 hcase44
                  omega
            ·
              rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase010b hcase031a hcase101a hcase101b hcase411a hcase040b hcase400b hcase00 hcase02 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase031a hcase031b hcase101a hcase101b hcase411a hcase040a hcase040b hcase401a hcase00 hcase02 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase010a hcase010b hcase031a hcase101a hcase101b hcase411a hcase411b hcase041a hcase00 hcase02 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase40 hcase42 hcase43 hcase44
                omega
      ·
        rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
        ·
          rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
          ·
            rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
            ·
              rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                        ·
                          clear hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase011b hcase400a hcase400b hcase320a hcase320b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase110b hcase130b hcase140b hcase100b hcase00 hcase12 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase400a hcase400b hcase320a hcase320b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase110b hcase130b hcase140b hcase101a hcase00 hcase12 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut66 hcut101 hcut1 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase120a hcase120b hcase311a hcase330b hcase341a hcase011a hcase400a hcase400b hcase320a hcase320b hcase040b hcase020b hcase030b hcase110a hcase110b hcase130a hcase130b hcase00 hcase10 hcase12 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
                        omega
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                        ·
                          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                          ·
                            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase011b hcase400a hcase400b hcase320a hcase320b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase110b hcase131a hcase140b hcase410a hcase410b hcase420a hcase420b hcase100b hcase00 hcase12 hcase30 hcase31 hcase43 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase011b hcase400b hcase320a hcase320b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase110b hcase131a hcase140b hcase410b hcase420b hcase101a hcase00 hcase12 hcase30 hcase31 hcase43 hcase44
                              omega
                          ·
                            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                            ·
                              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase011b hcase400a hcase400b hcase320a hcase320b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase110b hcase131a hcase140b hcase410a hcase410b hcase421a hcase421b hcase430a hcase430b hcase100b hcase00 hcase12 hcase30 hcase31 hcase44
                                omega
                              ·
                                clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase400b hcase320a hcase320b hcase040b hcase020b hcase030b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase410a hcase410b hcase421a hcase430b hcase101a hcase00 hcase12 hcase30 hcase31 hcase44
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase011b hcase400a hcase400b hcase320a hcase320b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase410a hcase410b hcase421a hcase431a hcase00 hcase10 hcase12 hcase30 hcase31 hcase44
                              omega
                        ·
                          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120b hcase311a hcase330b hcase341a hcase400a hcase400b hcase320b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase110b hcase131a hcase140a hcase140b hcase100b hcase00 hcase12 hcase30 hcase31 hcase42 hcase43 hcase44
                            omega
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              clear hn4 hsum_nat0 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut41 hcut77 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120b hcase311a hcase330b hcase341a hcase400b hcase320b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase110b hcase131a hcase140a hcase140b hcase411a hcase101a hcase420b hcase00 hcase12 hcase30 hcase31 hcase43 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase011b hcase400a hcase400b hcase320a hcase320b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase110a hcase110b hcase131a hcase131b hcase140a hcase140b hcase411a hcase101a hcase101b hcase421a hcase00 hcase12 hcase30 hcase31 hcase43 hcase44
                              omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut66 hcut101 hcut1 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase120a hcase120b hcase311a hcase330b hcase341a hcase011a hcase400a hcase400b hcase320a hcase320b hcase040b hcase020b hcase030b hcase110a hcase110b hcase131a hcase131b hcase00 hcase10 hcase12 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
                        omega
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase011b hcase400a hcase400b hcase320a hcase320b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase111a hcase111b hcase100b hcase00 hcase12 hcase13 hcase14 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
                      omega
                    ·
                      rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                      ·
                        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase011a hcase400b hcase320a hcase320b hcase040b hcase020b hcase030b hcase111a hcase111b hcase101a hcase101b hcase140a hcase140b hcase130a hcase130b hcase430b hcase420b hcase00 hcase12 hcase30 hcase31 hcase41 hcase44
                              omega
                            ·
                              clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase400b hcase320a hcase320b hcase040b hcase020b hcase030b hcase111a hcase111b hcase101a hcase140a hcase140b hcase130a hcase130b hcase430b hcase421a hcase00 hcase12 hcase30 hcase31 hcase41 hcase44
                              omega
                          ·
                            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                            ·
                              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                              ·
                                clear hn4 hsum_nat0 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase011b hcase400b hcase320a hcase320b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase111a hcase101a hcase140b hcase130b hcase431a hcase420b hcase410b hcase00 hcase12 hcase30 hcase31 hcase44
                                omega
                              ·
                                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase011b hcase400a hcase400b hcase320a hcase320b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase111a hcase111b hcase101a hcase101b hcase140a hcase140b hcase130a hcase130b hcase431a hcase420a hcase420b hcase411a hcase00 hcase12 hcase30 hcase31 hcase44
                                omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase011b hcase400a hcase400b hcase320a hcase320b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase111a hcase111b hcase101a hcase101b hcase140a hcase140b hcase130a hcase130b hcase431a hcase421a hcase00 hcase12 hcase30 hcase31 hcase41 hcase44
                              omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase011b hcase400a hcase400b hcase320a hcase320b hcase040a hcase040b hcase020a hcase020b hcase030a hcase030b hcase111a hcase101a hcase140b hcase131a hcase00 hcase12 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat4 hcut66 hcut101 hcut1 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase120a hcase120b hcase311a hcase330b hcase341a hcase011a hcase400a hcase400b hcase320a hcase320b hcase040b hcase020b hcase030b hcase111a hcase111b hcase101a hcase101b hcase00 hcase12 hcase13 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
                        omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase400a hcase400b hcase320a hcase320b hcase040a hcase040b hcase020a hcase020b hcase031a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase400a hcase400b hcase320a hcase320b hcase040a hcase040b hcase021a hcase00 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase400a hcase400b hcase320a hcase320b hcase041a hcase00 hcase02 hcase03 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase330a hcase330b hcase341a hcase011a hcase011b hcase400a hcase400b hcase321a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
            omega
        ·
          rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
          ·
            rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
            ·
              rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase401a hcase401b hcase420a hcase420b hcase430a hcase430b hcase440b hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase41
                omega
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase011a hcase401a hcase420b hcase430b hcase441a hcase020b hcase030b hcase040b hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase41
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase401a hcase401b hcase420a hcase420b hcase430a hcase430b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase041a hcase00 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase41
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase401a hcase401b hcase420a hcase420b hcase430a hcase430b hcase441a hcase441b hcase020a hcase020b hcase031a hcase00 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase41
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase401a hcase401b hcase420a hcase420b hcase430a hcase430b hcase441a hcase441b hcase021a hcase00 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase41
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase011b hcase401a hcase420a hcase420b hcase431a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase41 hcase44
              omega
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase330a hcase330b hcase341a hcase341b hcase011a hcase011b hcase401a hcase421a hcase00 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase32 hcase41 hcase43 hcase44
            omega
  ·
    rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
    ·
      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
      ·
        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
        ·
          rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase130a hcase130b hcase100b hcase00 hcase01 hcase02 hcase03 hcase04 hcase11 hcase12 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat0 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301b hcase120b hcase311b hcase331b hcase320a hcase320b hcase340a hcase340b hcase130b hcase101a hcase110b hcase140b hcase010a hcase010b hcase420b hcase400b hcase410b hcase00 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase43 hcase44
                        omega
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                          ·
                            clear hn4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301b hcase120b hcase311a hcase311b hcase320a hcase320b hcase340a hcase340b hcase130b hcase101a hcase110a hcase110b hcase140a hcase140b hcase010b hcase420b hcase400b hcase411a hcase430b hcase040b hcase00 hcase02 hcase03 hcase12 hcase30 hcase31 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase130a hcase130b hcase101a hcase101b hcase110a hcase110b hcase140b hcase010a hcase010b hcase420a hcase420b hcase400a hcase400b hcase411a hcase411b hcase430a hcase430b hcase00 hcase02 hcase03 hcase12 hcase30 hcase31 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase130a hcase130b hcase101a hcase101b hcase110a hcase110b hcase140a hcase140b hcase010a hcase010b hcase420a hcase420b hcase400a hcase400b hcase411a hcase431a hcase00 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase44
                          omega
                    ·
                      rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                      ·
                        rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                        ·
                          rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                          ·
                            clear hn4 hsum_nat0 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120b hcase311b hcase331b hcase320a hcase320b hcase340a hcase340b hcase130b hcase101a hcase110b hcase140b hcase010a hcase010b hcase420b hcase401a hcase040a hcase040b hcase440b hcase410b hcase00 hcase02 hcase03 hcase12 hcase30 hcase31 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase130a hcase130b hcase101a hcase101b hcase110a hcase110b hcase140a hcase140b hcase010a hcase010b hcase420a hcase420b hcase401a hcase040a hcase040b hcase440a hcase440b hcase411a hcase00 hcase02 hcase03 hcase12 hcase30 hcase31 hcase43
                            omega
                        ·
                          rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                          ·
                            rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                            ·
                              clear hn4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase301a hcase301b hcase120b hcase311b hcase320a hcase320b hcase340a hcase340b hcase130b hcase101a hcase110a hcase110b hcase140a hcase140b hcase010b hcase420b hcase401a hcase040b hcase441a hcase430b hcase410b hcase00 hcase02 hcase03 hcase12 hcase30 hcase31
                              omega
                            ·
                              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase130a hcase130b hcase101a hcase101b hcase110a hcase110b hcase140a hcase140b hcase010a hcase010b hcase420a hcase420b hcase401a hcase040a hcase040b hcase441a hcase441b hcase430a hcase430b hcase411a hcase00 hcase02 hcase03 hcase12 hcase30 hcase31
                              omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase130a hcase130b hcase101a hcase101b hcase110a hcase110b hcase140a hcase140b hcase010a hcase010b hcase420a hcase420b hcase401a hcase040a hcase040b hcase441a hcase441b hcase431a hcase00 hcase02 hcase03 hcase12 hcase30 hcase31 hcase41
                            omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase130a hcase130b hcase101a hcase101b hcase110a hcase110b hcase140b hcase010a hcase010b hcase420a hcase420b hcase401a hcase401b hcase00 hcase02 hcase03 hcase12 hcase30 hcase31 hcase41 hcase43 hcase44
                        omega
                  ·
                    rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                    ·
                      rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                      ·
                        rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase320a hcase320b hcase340a hcase340b hcase130a hcase130b hcase101a hcase110a hcase110b hcase140a hcase140b hcase010b hcase421a hcase430b hcase400b hcase040b hcase00 hcase02 hcase03 hcase12 hcase30 hcase31 hcase41 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut60 hcut7 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase320a hcase320b hcase340a hcase340b hcase130a hcase130b hcase101a hcase110a hcase110b hcase140a hcase140b hcase010b hcase421a hcase430b hcase400b hcase041a hcase00 hcase02 hcase03 hcase12 hcase30 hcase31 hcase41 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase130a hcase130b hcase101a hcase101b hcase110a hcase110b hcase140a hcase140b hcase010a hcase010b hcase421a hcase430a hcase430b hcase401a hcase00 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase41 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase130a hcase130b hcase101a hcase101b hcase110a hcase110b hcase140a hcase140b hcase010a hcase010b hcase421a hcase431a hcase00 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase40 hcase41 hcase44
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase130b hcase101a hcase110b hcase140b hcase00 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120b hcase311a hcase311b hcase320a hcase320b hcase340a hcase340b hcase130b hcase101a hcase110a hcase110b hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120b hcase311a hcase311b hcase320a hcase320b hcase340a hcase340b hcase130b hcase101a hcase111a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
            ·
              rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
              ·
                rcases hcase04 with ⟨hcase040a, hcase040b⟩ | ⟨hcase041a, hcase041b⟩
                ·
                  rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase110b hcase140b hcase400a hcase400b hcase040a hcase040b hcase100b hcase00 hcase01 hcase02 hcase03 hcase12 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase110b hcase140b hcase400b hcase040a hcase040b hcase101a hcase420b hcase410b hcase00 hcase01 hcase02 hcase03 hcase12 hcase30 hcase31 hcase43 hcase44
                        omega
                      ·
                        rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                        ·
                          rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase320a hcase320b hcase340a hcase340b hcase131a hcase131b hcase110a hcase110b hcase140a hcase140b hcase400b hcase040b hcase101a hcase420a hcase420b hcase411a hcase430b hcase010b hcase00 hcase02 hcase03 hcase12 hcase30 hcase31 hcase44
                            omega
                          ·
                            clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut86 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340b hcase131a hcase131b hcase110a hcase110b hcase140a hcase140b hcase400b hcase040b hcase101a hcase420a hcase420b hcase411a hcase430b hcase011a hcase00 hcase02 hcase03 hcase12 hcase30 hcase31 hcase44
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase131b hcase110a hcase110b hcase140a hcase140b hcase400a hcase400b hcase040a hcase040b hcase101a hcase101b hcase420a hcase420b hcase411a hcase431a hcase00 hcase01 hcase02 hcase03 hcase12 hcase30 hcase31 hcase44
                          omega
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        rcases hcase01 with ⟨hcase010a, hcase010b⟩ | ⟨hcase011a, hcase011b⟩
                        ·
                          clear hn4 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340b hcase131b hcase110a hcase110b hcase140a hcase140b hcase400b hcase040b hcase101a hcase101b hcase421a hcase430b hcase010b hcase00 hcase02 hcase03 hcase12 hcase30 hcase31 hcase41 hcase44
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut86 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340b hcase131a hcase131b hcase110a hcase110b hcase140a hcase140b hcase400b hcase040b hcase101a hcase421a hcase430b hcase011a hcase00 hcase02 hcase03 hcase12 hcase30 hcase31 hcase41 hcase44
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase131b hcase110a hcase110b hcase140a hcase140b hcase400a hcase400b hcase040a hcase040b hcase101a hcase101b hcase421a hcase431a hcase00 hcase01 hcase02 hcase03 hcase12 hcase30 hcase31 hcase41 hcase44
                        omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase131b hcase110a hcase110b hcase140b hcase400a hcase400b hcase00 hcase01 hcase02 hcase03 hcase10 hcase12 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131b hcase110a hcase110b hcase140a hcase140b hcase401a hcase440b hcase430b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase12 hcase30 hcase31 hcase41 hcase42
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase131b hcase110a hcase110b hcase140a hcase140b hcase401a hcase440a hcase440b hcase431a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase12 hcase30 hcase31 hcase41 hcase42
                    omega
                ·
                  rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase110b hcase140b hcase401a hcase401b hcase441a hcase441b hcase430a hcase430b hcase100b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase41 hcase42
                      omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hcut66 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase110b hcase140a hcase140b hcase401a hcase441a hcase430b hcase101a hcase410b hcase420b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31
                          omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase131b hcase110a hcase110b hcase140a hcase140b hcase401a hcase441a hcase441b hcase430a hcase430b hcase101a hcase101b hcase410a hcase410b hcase421a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase131b hcase110a hcase110b hcase140a hcase140b hcase401a hcase441a hcase441b hcase430a hcase430b hcase101a hcase101b hcase411a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase42
                        omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase131b hcase110a hcase110b hcase140a hcase140b hcase401a hcase441a hcase441b hcase431a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase12 hcase30 hcase31 hcase41 hcase42
                    omega
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase110b hcase141a hcase100b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase40 with ⟨hcase400a, hcase400b⟩ | ⟨hcase401a, hcase401b⟩
                ·
                  clear hn4 hsum_nat0 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120b hcase311a hcase331a hcase320b hcase340b hcase131a hcase110a hcase110b hcase101a hcase400b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase41 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase43 with ⟨hcase430a, hcase430b⟩ | ⟨hcase431a, hcase431b⟩
                      ·
                        clear hn4 hsum_nat0 hcut66 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut50 hcut76 hcut94 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120b hcase311a hcase331a hcase320b hcase340b hcase131a hcase110b hcase141a hcase101a hcase401a hcase420b hcase410b hcase430b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase44
                        omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase131b hcase110a hcase110b hcase141a hcase141b hcase101a hcase101b hcase401a hcase420a hcase420b hcase410a hcase410b hcase431a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase44
                        omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase131b hcase110a hcase110b hcase141a hcase141b hcase101a hcase101b hcase401a hcase420a hcase420b hcase411a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase131b hcase110a hcase110b hcase141a hcase141b hcase101a hcase101b hcase401a hcase421a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase41 hcase43 hcase44
                    omega
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase131b hcase111a hcase111b hcase100b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase111a hcase101a hcase140b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount3 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase301b hcase120a hcase120b hcase311a hcase311b hcase331a hcase331b hcase320a hcase320b hcase340a hcase340b hcase131a hcase111a hcase101a hcase141a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase331a hcase320a hcase320b hcase341a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
        omega
    ·
      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut66 hcut101 hcut1 hcut97 hcut100 hcut5 hcut12 hcut60 hcut7 hcut0 hcut50 hcut76 hcut94 hcut78 hcut95 hcut85 hcut62 hcut38 hcut41 hcut77 hcut79 hcut30 hcut14 hcut68 hcut4 hcut8 hcut99 hcut11 hcut86 hcut43 hcut6 hcut21 hcut96 hcut55 hcut84 hcut31 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hmincount0 hmincount1 hmincount4 hminend0 hminend4 hcase001a hcase001b hcase301a hcase120a hcase120b hcase311a hcase331a hcase321a hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43 hcase44
      omega

#print axioms symbolic_v2_mask1023_integer_shard006
end Jsp404.SixExactFloorKernel
