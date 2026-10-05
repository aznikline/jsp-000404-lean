import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Jsp404.SixExactFloorKernel
set_option maxHeartbeats 16000000 in
theorem symbolic_mask202_integer_shard003 (n s00 s01 s02 s03 s04 s10 s11 s12 s13 s14 s30 s31 s32 s33 s34 s40 s41 s42 s43 s44 u00 u01 u02 u03 u04 u10 u11 u12 u13 u14 u30 u31 u32 u33 u34 u40 u41 u42 u43 u44 : ℕ)
    (hn4 : 4 ≤ n)
    (hsum_nat0 : (s00 + (s01 + (s02 + (s03 + (s04))))) + 2 = n)
    (hsum_nat1 : (s10 + (s11 + (s12 + (s13 + (s14))))) + 3 = n)
    (hsum_nat3 : (s30 + (s31 + (s32 + (s33 + (s34))))) + 3 = n)
    (hsum_nat4 : (s40 + (s41 + (s42 + (s43 + (s44))))) + 2 = n)
    (hcut49 : (s12 + s30 + s34 + u12 + u30 + u34) + 1 ≤ (n))
    (hcut16 : (s34 + u34) + 1 ≤ (s44 + 2))
    (hcut0 : (s02 + s03 + s11 + s30 + s31 + s34 + s41 + s42 + s43 + u02 + u03 + u11 + u30 + u31 + u34 + u41 + u42 + u43) + 1 ≤ (n + 1))
    (hcut23 : (s12 + s30 + s31 + u12 + u30 + u31 + 1) + 1 ≤ (n))
    (hcut46 : (s04 + s10 + s40 + s44 + u04 + u10 + u40 + u44) + 1 ≤ (2 * n))
    (hcut67 : (s00 + s01 + s12 + s44 + u00 + u01 + u12 + u44) + 1 ≤ (n + 2))
    (hcut8 : (s00 + s33 + u00 + u33) + 1 ≤ (n + 1))
    (hcut31 : (s44 + u44) + 1 ≤ (s34 + 3))
    (hcut29 : (s10 + s12 + s44 + u10 + u12 + u44) + 1 ≤ (n + 1))
    (hcut39 : (s11 + s30 + s42 + u11 + u30 + u42 + 1) + 1 ≤ (n))
    (hcut5 : (s32 + u32) + 1 ≤ (s11 + 2))
    (hcut54 : (s00 + s03 + s04 + u00 + u03 + u04) + 1 ≤ (n + 1))
    (hcut62 : (s11 + s13 + s14 + s31 + u11 + u13 + u14 + u31 + 1) + 1 ≤ (n))
    (hcut52 : (s12 + s13 + s14 + s31 + u12 + u13 + u14 + u31 + 1) + 1 ≤ (n))
    (hcut3 : (s02 + s03 + s41 + s42 + u02 + u03 + u41 + u42) + 1 ≤ (s12 + 2))
    (hcut42 : (s13 + s14 + u13 + u14 + 2) + 1 ≤ (n))
    (hcut61 : (s10 + s13 + s14 + u10 + u13 + u14 + 1) + 1 ≤ (n))
    (hcut15 : (s12 + s31 + u12 + u31 + 2) + 1 ≤ (n))
    (hcut36 : (s40 + s41 + u40 + u41 + 1) + 1 ≤ (n))
    (hcut68 : (s10 + s32 + u10 + u32) + 1 ≤ (s00 + 2))
    (hcut4 : (s00 + s04 + s33 + s40 + s44 + u00 + u04 + u33 + u40 + u44) + 1 ≤ (2 * n + 2))
    (hcut63 : (s10 + s11 + s13 + s14 + u10 + u11 + u13 + u14) + 1 ≤ (n))
    (hcut73 : (s01 + s12 + s43 + u01 + u12 + u43) + 1 ≤ (s33 + 2))
    (hcut9 : (s00 + s04 + s33 + s40 + u00 + u04 + u33 + u40) + 1 ≤ (2 * n + 1))
    (hcut19 : (s00 + s44 + u00 + u44) + 1 ≤ (n + 1))
    (hcut69 : (s11 + s12 + s31 + u11 + u12 + u31 + 1) + 1 ≤ (n))
    (hcut56 : (s11 + s12 + s13 + s14 + u11 + u12 + u13 + u14) + 1 ≤ (n))
    (hcut65 : (s01 + s02 + s43 + u01 + u02 + u43) + 1 ≤ (s33 + 1))
    (hcut44 : (s11 + s14 + u11 + u14 + 2) + 1 ≤ (n))
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
    (hcase401a : 1 ≤ s40)
    (hcase401b : u40 = 1)
    (hcase430a : s43 = 0)
    (hcase430b : u43 = 0)
    (hcase121a : 1 ≤ s12)
    (hcase121b : u12 = 1)
    (hcase010a : s01 = 0)
    (hcase010b : u01 = 0)
    (hcase310a : s31 = 0)
    (hcase310b : u31 = 0)
    : False := by
  rcases hcase32 with ⟨hcase320a, hcase320b⟩ | ⟨hcase321a, hcase321b⟩
  ·
    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
    ·
      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
      ·
        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
        ·
          rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
          ·
            rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase020a hcase020b hcase000a hcase000b hcase100b hcase140b hcase130b hcase110b hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase020a hcase020b hcase000a hcase000b hcase100b hcase140b hcase130b hcase111a hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase020a hcase020b hcase000a hcase000b hcase100b hcase140a hcase140b hcase131a hcase110b hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase020a hcase020b hcase000a hcase000b hcase100b hcase140a hcase140b hcase131a hcase111a hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase020a hcase020b hcase000a hcase000b hcase100b hcase141a hcase110b hcase01 hcase04 hcase12 hcase13 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase020a hcase020b hcase000a hcase000b hcase100b hcase141a hcase111a hcase01 hcase04 hcase12 hcase13 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase020a hcase020b hcase000b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                omega
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hsum_nat0 hsum_nat1 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310b hcase320b hcase340b hcase410a hcase410b hcase030a hcase030b hcase020a hcase020b hcase001a hcase001b hcase300b hcase330b hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase010b hcase310a hcase310b hcase320b hcase340b hcase410b hcase030b hcase020b hcase001a hcase300b hcase331a hcase420b hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43 hcase44
                    omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut36 hcut68 hcut4 hcut63 hcut73 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase410a hcase410b hcase030a hcase030b hcase020a hcase020b hcase001a hcase300b hcase331a hcase421a hcase440b hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase410a hcase410b hcase030a hcase030b hcase020a hcase020b hcase001a hcase300b hcase331a hcase421a hcase441a hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                      omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310b hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase020a hcase020b hcase001a hcase001b hcase301a hcase330b hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                  ·
                    clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase010b hcase310a hcase310b hcase320b hcase340b hcase410b hcase030b hcase020b hcase001a hcase301a hcase331a hcase420b hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43 hcase44
                    omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase121b hcase010b hcase310b hcase320b hcase340b hcase410b hcase030b hcase020b hcase001a hcase301a hcase331a hcase421a hcase440b hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase121b hcase010b hcase310b hcase320b hcase340b hcase410b hcase030b hcase020b hcase001a hcase301a hcase331a hcase421a hcase441a hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                      omega
          ·
            rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase430b hcase121a hcase010a hcase010b hcase310b hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase440b hcase330b hcase00 hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase42 hcase43
                omega
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                      ·
                        rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                        ·
                          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase440a hcase440b hcase331a hcase331b hcase300a hcase300b hcase000a hcase000b hcase110b hcase100b hcase130b hcase140b hcase01 hcase04 hcase12 hcase31 hcase40 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase440a hcase440b hcase331a hcase331b hcase300a hcase300b hcase000a hcase000b hcase110b hcase100b hcase130a hcase130b hcase141a hcase01 hcase04 hcase12 hcase31 hcase40 hcase42 hcase43
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase440a hcase440b hcase331a hcase331b hcase300a hcase300b hcase000a hcase000b hcase110b hcase100b hcase131a hcase01 hcase04 hcase12 hcase14 hcase31 hcase40 hcase42 hcase43
                          omega
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase440a hcase440b hcase331a hcase331b hcase300a hcase300b hcase000b hcase110a hcase110b hcase01 hcase04 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                        omega
                    ·
                      clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase440b hcase331a hcase300b hcase000a hcase000b hcase01 hcase04 hcase10 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                      omega
                  ·
                    clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut36 hcut68 hcut4 hcut63 hcut73 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase440b hcase331a hcase300b hcase001a hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                    omega
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                        ·
                          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase440a hcase440b hcase331a hcase331b hcase000a hcase000b hcase100b hcase110b hcase140b hcase130b hcase01 hcase04 hcase12 hcase31 hcase40 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase440a hcase440b hcase331a hcase331b hcase301a hcase301b hcase000a hcase000b hcase100b hcase110b hcase140a hcase140b hcase131a hcase01 hcase04 hcase12 hcase31 hcase40 hcase42 hcase43
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase440a hcase440b hcase331a hcase331b hcase301a hcase301b hcase000a hcase000b hcase100b hcase110b hcase141a hcase01 hcase04 hcase12 hcase13 hcase31 hcase40 hcase42 hcase43
                          omega
                      ·
                        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                        ·
                          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                          ·
                            clear hn4 hcut49 hcut16 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase440b hcase331a hcase000a hcase000b hcase100b hcase111a hcase140b hcase130b hcase01 hcase04 hcase12 hcase31 hcase40 hcase42 hcase43
                            omega
                          ·
                            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase440a hcase440b hcase331a hcase331b hcase301a hcase301b hcase000a hcase000b hcase100b hcase111a hcase140a hcase140b hcase131a hcase01 hcase04 hcase12 hcase31 hcase40 hcase42 hcase43
                            omega
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase440a hcase440b hcase331a hcase331b hcase301a hcase301b hcase000a hcase000b hcase100b hcase111a hcase141a hcase01 hcase04 hcase12 hcase13 hcase31 hcase40 hcase42 hcase43
                          omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase440a hcase440b hcase331a hcase331b hcase301a hcase301b hcase000b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                      omega
                  ·
                    clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase440b hcase331a hcase301a hcase001a hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                    omega
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase441a hcase441b hcase100b hcase110b hcase130b hcase140b hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase441a hcase441b hcase100b hcase110b hcase130a hcase130b hcase141a hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase441a hcase441b hcase100b hcase110b hcase131a hcase00 hcase01 hcase04 hcase12 hcase14 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43
                    omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase441a hcase441b hcase100b hcase111a hcase130b hcase140b hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase441a hcase441b hcase100b hcase111a hcase130a hcase130b hcase141a hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43
                      omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase441a hcase441b hcase100b hcase111a hcase131a hcase00 hcase01 hcase04 hcase12 hcase14 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43
                    omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut49 hcut16 hcut0 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310a hcase310b hcase320b hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase441a hcase441b hcase101a hcase101b hcase330b hcase00 hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase42 hcase43
                  omega
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase021b hcase441a hcase441b hcase331a hcase331b hcase000b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase42 hcase43
                    omega
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      clear hn4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase121b hcase010b hcase310b hcase320b hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase441a hcase101b hcase331a hcase001a hcase300b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase410a hcase410b hcase030a hcase030b hcase021a hcase441a hcase101a hcase101b hcase331a hcase001a hcase301a hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                      omega
        ·
          rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase031a hcase031b hcase000a hcase000b hcase100b hcase140b hcase130b hcase110b hcase01 hcase02 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase031a hcase031b hcase000a hcase000b hcase100b hcase140b hcase130b hcase111a hcase01 hcase02 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase031a hcase031b hcase000a hcase000b hcase100b hcase140a hcase140b hcase131a hcase110b hcase01 hcase02 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase031a hcase031b hcase000a hcase000b hcase100b hcase140a hcase140b hcase131a hcase111a hcase01 hcase02 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase031a hcase031b hcase000a hcase000b hcase100b hcase141a hcase110b hcase01 hcase02 hcase04 hcase12 hcase13 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase031a hcase031b hcase000a hcase000b hcase100b hcase141a hcase111a hcase01 hcase02 hcase04 hcase12 hcase13 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase031a hcase031b hcase000b hcase01 hcase02 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase031a hcase031b hcase001a hcase001b hcase130b hcase300a hcase300b hcase100b hcase140b hcase110b hcase01 hcase02 hcase04 hcase12 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase031a hcase031b hcase001a hcase001b hcase130b hcase300a hcase300b hcase100b hcase140b hcase111a hcase01 hcase02 hcase04 hcase12 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                      omega
                  ·
                    rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase031a hcase001a hcase130a hcase130b hcase300a hcase300b hcase100a hcase100b hcase141a hcase141b hcase020b hcase01 hcase04 hcase11 hcase12 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase410a hcase410b hcase031a hcase001a hcase130a hcase130b hcase300b hcase100a hcase100b hcase021a hcase01 hcase04 hcase11 hcase12 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                      omega
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase031a hcase001a hcase130a hcase130b hcase300a hcase300b hcase101a hcase101b hcase020b hcase01 hcase04 hcase11 hcase12 hcase14 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hsum_nat0 hsum_nat1 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310b hcase320b hcase340b hcase410a hcase410b hcase031a hcase031b hcase001a hcase001b hcase130a hcase130b hcase300b hcase101a hcase101b hcase021a hcase021b hcase330b hcase01 hcase04 hcase11 hcase12 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase121b hcase010b hcase310b hcase320b hcase340b hcase410a hcase410b hcase031a hcase001a hcase130a hcase130b hcase300b hcase101b hcase021a hcase331a hcase01 hcase04 hcase11 hcase12 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                      omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut49 hcut16 hcut0 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310a hcase310b hcase320b hcase340b hcase410a hcase410b hcase031a hcase031b hcase001a hcase001b hcase130a hcase130b hcase301a hcase330b hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase031a hcase001a hcase130a hcase130b hcase301a hcase301b hcase331a hcase331b hcase020b hcase01 hcase04 hcase10 hcase11 hcase12 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase410a hcase410b hcase031a hcase001a hcase130a hcase130b hcase301a hcase331a hcase021a hcase01 hcase04 hcase10 hcase11 hcase12 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                    omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat1 hsum_nat4 hcut49 hcut16 hcut0 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase401b hcase430a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase410a hcase410b hcase001a hcase131a hcase131b hcase330b hcase01 hcase02 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase40 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase410a hcase410b hcase031a hcase001a hcase131a hcase131b hcase331a hcase331b hcase020b hcase01 hcase04 hcase10 hcase11 hcase12 hcase14 hcase30 hcase31 hcase40 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                  ·
                    clear hn4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase121b hcase010b hcase310b hcase320b hcase340b hcase410a hcase410b hcase031a hcase001a hcase131b hcase331a hcase021a hcase300b hcase01 hcase04 hcase10 hcase11 hcase12 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase410a hcase410b hcase031a hcase001a hcase131a hcase131b hcase331a hcase021a hcase301a hcase01 hcase04 hcase10 hcase11 hcase12 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                    omega
      ·
        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
        ·
          rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase020a hcase020b hcase000a hcase000b hcase130b hcase140b hcase100b hcase110b hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase020a hcase020b hcase000a hcase000b hcase130b hcase140b hcase100b hcase111a hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase020a hcase020b hcase000b hcase130a hcase130b hcase140a hcase140b hcase01 hcase03 hcase04 hcase11 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase020a hcase020b hcase000a hcase000b hcase130a hcase130b hcase141a hcase100b hcase110b hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase020a hcase020b hcase000a hcase000b hcase130a hcase130b hcase141a hcase100b hcase111a hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase020a hcase020b hcase000b hcase130a hcase130b hcase141a hcase141b hcase01 hcase03 hcase04 hcase11 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase020a hcase020b hcase000a hcase000b hcase131a hcase100b hcase110b hcase01 hcase03 hcase04 hcase12 hcase14 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase020a hcase020b hcase000a hcase000b hcase131a hcase100b hcase111a hcase01 hcase03 hcase04 hcase12 hcase14 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                  omega
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase020a hcase020b hcase000b hcase131a hcase131b hcase01 hcase03 hcase04 hcase11 hcase12 hcase14 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                omega
          ·
            rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310b hcase320b hcase340b hcase020a hcase020b hcase001a hcase001b hcase030a hcase030b hcase300b hcase420a hcase420b hcase330b hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase430b hcase121a hcase121b hcase010b hcase310b hcase320b hcase340b hcase411a hcase020b hcase001a hcase030b hcase300b hcase420b hcase331a hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43 hcase44
                    omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320b hcase340b hcase020a hcase020b hcase001a hcase001b hcase030a hcase030b hcase300b hcase330b hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase411a hcase020a hcase020b hcase001a hcase030a hcase030b hcase300b hcase421a hcase331a hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43 hcase44
                    omega
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase430b hcase121a hcase010a hcase010b hcase310b hcase320b hcase340a hcase340b hcase020a hcase020b hcase001a hcase001b hcase030a hcase030b hcase301a hcase440b hcase330b hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase411a hcase020a hcase020b hcase001a hcase030a hcase030b hcase301a hcase440b hcase331a hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                    omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut49 hcut16 hcut0 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310a hcase310b hcase320b hcase340b hcase411a hcase411b hcase020a hcase020b hcase001a hcase001b hcase030a hcase030b hcase301a hcase441a hcase441b hcase330b hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase411a hcase020a hcase020b hcase001a hcase030a hcase030b hcase301a hcase441a hcase331a hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                    omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase020b hcase001a hcase031a hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase021a hcase021b hcase000a hcase000b hcase100b hcase110b hcase140b hcase130b hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase021a hcase021b hcase000a hcase000b hcase100b hcase110b hcase140a hcase140b hcase131a hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase021a hcase021b hcase000a hcase000b hcase100b hcase110b hcase141a hcase01 hcase03 hcase04 hcase12 hcase13 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase021a hcase021b hcase000a hcase000b hcase100b hcase111a hcase130b hcase140b hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase021a hcase021b hcase000a hcase000b hcase100b hcase111a hcase130a hcase130b hcase141a hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase021a hcase021b hcase000a hcase000b hcase100b hcase111a hcase131a hcase01 hcase03 hcase04 hcase12 hcase14 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                  omega
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase021a hcase021b hcase000b hcase01 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase021a hcase021b hcase001a hcase001b hcase300a hcase300b hcase100b hcase130b hcase140b hcase110b hcase01 hcase03 hcase04 hcase12 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase340a hcase340b hcase411a hcase411b hcase021a hcase021b hcase001a hcase001b hcase300a hcase300b hcase100b hcase130b hcase140b hcase111a hcase01 hcase03 hcase04 hcase12 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                      omega
                  ·
                    clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase411a hcase021a hcase001a hcase300b hcase100a hcase100b hcase130a hcase130b hcase01 hcase03 hcase04 hcase11 hcase12 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                    omega
                ·
                  clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase411a hcase021a hcase001a hcase300b hcase100a hcase100b hcase01 hcase03 hcase04 hcase11 hcase12 hcase14 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                  omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase430b hcase121a hcase010a hcase010b hcase310b hcase320b hcase340b hcase001a hcase001b hcase300b hcase330b hcase01 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                  omega
                ·
                  clear hn4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase121b hcase010b hcase310b hcase320b hcase340b hcase411a hcase021a hcase001a hcase300b hcase101b hcase331a hcase01 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                  omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut49 hcut16 hcut0 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310a hcase310b hcase320b hcase340b hcase411a hcase411b hcase021a hcase021b hcase001a hcase001b hcase301a hcase330b hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                omega
              ·
                clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310a hcase310b hcase320b hcase340b hcase411a hcase021a hcase001a hcase301a hcase331a hcase01 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                omega
    ·
      rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
      ·
        rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
        ·
          rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase100b hcase140b hcase130b hcase110b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase341a hcase341b hcase100b hcase140b hcase130b hcase111a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase341a hcase341b hcase100b hcase140a hcase140b hcase131a hcase110b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase341a hcase341b hcase100b hcase140a hcase140b hcase131a hcase111a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase341a hcase341b hcase100b hcase141a hcase110b hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase13 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
          ·
            clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase341a hcase341b hcase100b hcase141a hcase111a hcase00 hcase01 hcase02 hcase03 hcase04 hcase12 hcase13 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
            omega
      ·
        rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
        ·
          rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
          ·
            rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310b hcase320b hcase341a hcase101a hcase101b hcase020a hcase020b hcase030a hcase030b hcase300a hcase300b hcase330b hcase00 hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43 hcase44
                omega
              ·
                rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase101a hcase101b hcase020a hcase020b hcase030a hcase030b hcase300a hcase300b hcase331a hcase331b hcase440b hcase00 hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43
                  omega
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase341a hcase341b hcase020a hcase020b hcase030a hcase030b hcase300a hcase300b hcase331a hcase331b hcase441a hcase441b hcase000b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43
                    omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hcut49 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase010b hcase310b hcase320b hcase341a hcase020b hcase030b hcase300b hcase331a hcase441a hcase001a hcase410b hcase420b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut49 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310b hcase320b hcase341a hcase020a hcase020b hcase030a hcase030b hcase300b hcase331a hcase441a hcase001a hcase410a hcase410b hcase421a hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                        omega
                    ·
                      clear hn4 hsum_nat1 hcut49 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310b hcase320b hcase341a hcase020a hcase020b hcase030a hcase030b hcase300b hcase331a hcase441a hcase001a hcase411a hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                      omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310b hcase320b hcase341a hcase101a hcase101b hcase020a hcase020b hcase030a hcase030b hcase301a hcase410a hcase410b hcase420a hcase420b hcase330b hcase00 hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43 hcase44
                    omega
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut49 hcut16 hcut0 hcut23 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase320a hcase320b hcase341a hcase341b hcase020b hcase030b hcase301a hcase301b hcase410b hcase420b hcase331a hcase331b hcase000b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43 hcase44
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase010b hcase310b hcase320b hcase341a hcase101a hcase101b hcase020b hcase030b hcase301a hcase410b hcase420b hcase331a hcase001a hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43 hcase44
                      omega
                ·
                  rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase101a hcase101b hcase020a hcase020b hcase030a hcase030b hcase301a hcase301b hcase410a hcase410b hcase421a hcase421b hcase440b hcase00 hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase40 hcase43
                    omega
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase341a hcase341b hcase020a hcase020b hcase030a hcase030b hcase301a hcase301b hcase410a hcase410b hcase421a hcase421b hcase441a hcase441b hcase000b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase40 hcase43
                      omega
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310b hcase320b hcase341a hcase101a hcase101b hcase020a hcase020b hcase030a hcase030b hcase301a hcase410a hcase410b hcase421a hcase421b hcase441a hcase441b hcase001a hcase001b hcase330b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310b hcase320b hcase341a hcase101a hcase101b hcase020a hcase020b hcase030a hcase030b hcase301a hcase410a hcase410b hcase421a hcase441a hcase001a hcase331a hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                        omega
              ·
                rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase341a hcase341b hcase020a hcase020b hcase030a hcase030b hcase301a hcase301b hcase411a hcase411b hcase000b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase40 hcase42 hcase43 hcase44
                  omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310b hcase320b hcase341a hcase101a hcase101b hcase020a hcase020b hcase030a hcase030b hcase301a hcase411a hcase411b hcase001a hcase001b hcase330b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43 hcase44
                    omega
                  ·
                    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase101a hcase101b hcase020a hcase020b hcase030a hcase030b hcase301a hcase301b hcase411a hcase411b hcase001a hcase001b hcase331a hcase331b hcase440b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310b hcase320b hcase341a hcase101a hcase101b hcase020a hcase020b hcase030a hcase030b hcase301a hcase411a hcase001a hcase331a hcase441a hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                      omega
          ·
            rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase341a hcase341b hcase020a hcase020b hcase031a hcase031b hcase000b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
            ·
              clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase320a hcase320b hcase341a hcase341b hcase101a hcase101b hcase020b hcase031a hcase001a hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43 hcase44
              omega
        ·
          rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase101a hcase101b hcase021a hcase021b hcase440b hcase00 hcase01 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43
            omega
          ·
            rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase341a hcase341b hcase101a hcase101b hcase441a hcase441b hcase330b hcase00 hcase01 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43
              omega
            ·
              rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase320a hcase320b hcase341a hcase341b hcase021a hcase021b hcase441a hcase441b hcase331a hcase331b hcase000b hcase01 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43
                omega
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  clear hn4 hsum_nat1 hcut49 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310b hcase320b hcase341a hcase021a hcase441a hcase331a hcase001a hcase300b hcase01 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43
                  omega
                ·
                  clear hn4 hsum_nat1 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310b hcase320b hcase341a hcase101a hcase101b hcase021a hcase441a hcase331a hcase001a hcase301a hcase01 hcase03 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43
                  omega
  ·
    rcases hcase44 with ⟨hcase440a, hcase440b⟩ | ⟨hcase441a, hcase441b⟩
    ·
      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
      ·
        rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase440b hcase340a hcase340b hcase420b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase43
          omega
        ·
          rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase440a hcase440b hcase340a hcase340b hcase421a hcase421b hcase330b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase43
            omega
          ·
            rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase440a hcase440b hcase340a hcase340b hcase421a hcase421b hcase331a hcase331b hcase110b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase43
              omega
            ·
              rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase440a hcase440b hcase340a hcase340b hcase421a hcase421b hcase331a hcase331b hcase111a hcase111b hcase000b hcase01 hcase02 hcase03 hcase04 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase43
                omega
              ·
                rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                ·
                  rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase121b hcase010b hcase310b hcase321a hcase440b hcase340b hcase421a hcase331a hcase111a hcase001a hcase030b hcase020b hcase410b hcase01 hcase04 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase440b hcase340a hcase340b hcase421a hcase331a hcase111a hcase111b hcase001a hcase030a hcase030b hcase020a hcase020b hcase411a hcase01 hcase04 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase43
                      omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase440b hcase340a hcase340b hcase421a hcase331a hcase111a hcase111b hcase001a hcase030a hcase030b hcase021a hcase01 hcase04 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase43
                    omega
                ·
                  clear hn4 hsum_nat1 hsum_nat3 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase440b hcase340a hcase340b hcase421a hcase331a hcase111a hcase111b hcase001a hcase031a hcase01 hcase02 hcase04 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase43
                  omega
      ·
        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase440b hcase00 hcase01 hcase02 hcase03 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43
        omega
    ·
      rcases hcase02 with ⟨hcase020a, hcase020b⟩ | ⟨hcase021a, hcase021b⟩
      ·
        rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
        ·
          rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
          ·
            rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase420a hcase420b hcase100b hcase130b hcase140b hcase110b hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase41 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase420a hcase420b hcase100b hcase130b hcase140b hcase111a hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase41 hcase43
                      omega
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase420a hcase420b hcase100a hcase100b hcase130a hcase130b hcase141a hcase141b hcase110b hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase41 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase420a hcase420b hcase100b hcase130a hcase130b hcase141a hcase111a hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase41 hcase43
                      omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase420a hcase420b hcase100a hcase100b hcase131a hcase131b hcase110b hcase00 hcase01 hcase04 hcase12 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase420a hcase420b hcase100b hcase131a hcase111a hcase00 hcase01 hcase04 hcase12 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase43
                    omega
              ·
                rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase420a hcase420b hcase101a hcase101b hcase410a hcase410b hcase330b hcase00 hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase43
                    omega
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase420a hcase420b hcase410a hcase410b hcase331a hcase331b hcase000b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase020b hcase030b hcase340a hcase340b hcase420b hcase101a hcase101b hcase410b hcase331a hcase001a hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase43
                      omega
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase020a hcase020b hcase030a hcase030b hcase340b hcase420b hcase101a hcase101b hcase411a hcase00 hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase43
                  omega
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase421a hcase421b hcase300a hcase300b hcase000b hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase31 hcase33 hcase40 hcase41 hcase43
                  omega
                ·
                  rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                  ·
                    rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase421a hcase421b hcase300a hcase300b hcase001a hcase001b hcase130a hcase130b hcase140a hcase140b hcase110b hcase01 hcase04 hcase10 hcase12 hcase31 hcase33 hcase40 hcase41 hcase43
                        omega
                      ·
                        rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase421a hcase421b hcase300a hcase300b hcase001a hcase001b hcase130b hcase140b hcase111a hcase100b hcase01 hcase04 hcase12 hcase31 hcase33 hcase40 hcase41 hcase43
                          omega
                        ·
                          clear hn4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase020a hcase020b hcase030a hcase030b hcase340b hcase421a hcase300b hcase001a hcase130b hcase140b hcase111a hcase101a hcase01 hcase04 hcase12 hcase31 hcase33 hcase40 hcase41 hcase43
                          omega
                    ·
                      rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase421a hcase421b hcase300a hcase300b hcase001a hcase001b hcase130a hcase130b hcase141a hcase141b hcase110b hcase01 hcase04 hcase10 hcase12 hcase31 hcase33 hcase40 hcase41 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310b hcase321a hcase441a hcase020a hcase020b hcase030a hcase030b hcase340b hcase421a hcase300b hcase001a hcase130a hcase130b hcase111a hcase01 hcase04 hcase10 hcase12 hcase31 hcase33 hcase40 hcase41 hcase43
                        omega
                  ·
                    rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase421a hcase421b hcase300a hcase300b hcase001a hcase001b hcase131a hcase131b hcase110b hcase01 hcase04 hcase10 hcase12 hcase14 hcase31 hcase33 hcase40 hcase41 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010b hcase310b hcase321a hcase441a hcase020a hcase020b hcase030a hcase030b hcase340b hcase421a hcase300b hcase001a hcase111a hcase01 hcase04 hcase10 hcase12 hcase14 hcase31 hcase33 hcase40 hcase41 hcase43
                      omega
              ·
                rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase421a hcase421b hcase301a hcase301b hcase110b hcase00 hcase01 hcase04 hcase10 hcase12 hcase13 hcase14 hcase31 hcase33 hcase40 hcase41 hcase43
                  omega
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase421a hcase421b hcase301a hcase301b hcase111a hcase111b hcase000b hcase01 hcase04 hcase10 hcase12 hcase13 hcase14 hcase31 hcase33 hcase40 hcase41 hcase43
                    omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310b hcase321a hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase340b hcase301a hcase111a hcase001a hcase001b hcase330b hcase01 hcase04 hcase10 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase43
                      omega
                    ·
                      rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                      ·
                        clear hn4 hsum_nat1 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase121b hcase010b hcase310b hcase321a hcase441a hcase020b hcase030b hcase340b hcase421a hcase301a hcase111a hcase001a hcase331a hcase410b hcase01 hcase04 hcase10 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut49 hcut16 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase321a hcase441a hcase020a hcase020b hcase030a hcase030b hcase340a hcase340b hcase421a hcase301a hcase111a hcase001a hcase331a hcase411a hcase01 hcase04 hcase10 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                        omega
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase341a hcase341b hcase100a hcase100b hcase110b hcase00 hcase01 hcase04 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43
                omega
              ·
                rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
                ·
                  rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase341a hcase341b hcase100b hcase111a hcase130b hcase140b hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase341a hcase341b hcase100b hcase111a hcase130a hcase130b hcase141a hcase00 hcase01 hcase04 hcase12 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43
                    omega
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase341a hcase341b hcase100b hcase111a hcase131a hcase00 hcase01 hcase04 hcase12 hcase14 hcase30 hcase31 hcase33 hcase40 hcase41 hcase42 hcase43
                  omega
            ·
              rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase341a hcase341b hcase101a hcase101b hcase330b hcase00 hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase40 hcase41 hcase42 hcase43
                omega
              ·
                rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase341a hcase341b hcase331a hcase331b hcase300a hcase300b hcase000b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43
                    omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        clear hn4 hsum_nat1 hcut49 hcut0 hcut23 hcut46 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase010a hcase010b hcase310b hcase321a hcase441a hcase020b hcase030b hcase341a hcase331a hcase300b hcase001a hcase410b hcase420b hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut49 hcut0 hcut23 hcut46 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010a hcase010b hcase310b hcase321a hcase441a hcase020a hcase020b hcase030a hcase030b hcase341a hcase331a hcase300b hcase001a hcase410a hcase410b hcase421a hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                        omega
                    ·
                      clear hn4 hsum_nat1 hcut49 hcut0 hcut23 hcut46 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010a hcase010b hcase310b hcase321a hcase441a hcase020a hcase020b hcase030a hcase030b hcase341a hcase331a hcase300b hcase001a hcase411a hcase01 hcase04 hcase11 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                      omega
                ·
                  rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase341a hcase341b hcase101a hcase101b hcase331a hcase331b hcase301a hcase301b hcase110b hcase00 hcase01 hcase04 hcase12 hcase13 hcase14 hcase31 hcase40 hcase41 hcase42 hcase43
                    omega
                  ·
                    rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                    ·
                      rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                      ·
                        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut49 hcut16 hcut0 hcut23 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase020b hcase030b hcase341a hcase341b hcase331a hcase331b hcase301a hcase301b hcase111a hcase111b hcase410b hcase420b hcase000b hcase01 hcase04 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase020b hcase030b hcase341a hcase341b hcase101a hcase101b hcase301a hcase301b hcase111a hcase111b hcase410b hcase420b hcase001a hcase01 hcase04 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                          omega
                      ·
                        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase341a hcase341b hcase331a hcase331b hcase301a hcase301b hcase111a hcase111b hcase410a hcase410b hcase421a hcase421b hcase000b hcase01 hcase04 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut49 hcut16 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase321a hcase441a hcase020a hcase020b hcase030a hcase030b hcase341a hcase101a hcase101b hcase331a hcase301a hcase111a hcase410a hcase410b hcase421a hcase001a hcase01 hcase04 hcase12 hcase13 hcase14 hcase31 hcase40 hcase43
                          omega
                    ·
                      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase030a hcase030b hcase341a hcase341b hcase331a hcase331b hcase301a hcase301b hcase111a hcase111b hcase411a hcase411b hcase000b hcase01 hcase04 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut49 hcut16 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase321a hcase441a hcase020a hcase020b hcase030a hcase030b hcase341a hcase101a hcase101b hcase331a hcase301a hcase111a hcase411a hcase001a hcase01 hcase04 hcase12 hcase13 hcase14 hcase31 hcase40 hcase42 hcase43
                        omega
        ·
          rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
          ·
            clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase020a hcase020b hcase031a hcase031b hcase000b hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43
            omega
          ·
            clear hn4 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase020b hcase031a hcase001a hcase01 hcase04 hcase10 hcase11 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43
            omega
      ·
        rcases hcase11 with ⟨hcase110a, hcase110b⟩ | ⟨hcase111a, hcase111b⟩
        ·
          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase021a hcase021b hcase110b hcase00 hcase01 hcase03 hcase04 hcase10 hcase12 hcase13 hcase14 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43
          omega
        ·
          rcases hcase14 with ⟨hcase140a, hcase140b⟩ | ⟨hcase141a, hcase141b⟩
          ·
            rcases hcase13 with ⟨hcase130a, hcase130b⟩ | ⟨hcase131a, hcase131b⟩
            ·
              rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
              ·
                clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase021a hcase021b hcase111a hcase140b hcase130b hcase100b hcase00 hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43
                omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase111a hcase111b hcase140a hcase140b hcase130a hcase130b hcase101a hcase101b hcase330b hcase00 hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43
                  omega
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase021a hcase021b hcase111a hcase140b hcase130b hcase101a hcase331a hcase331b hcase000b hcase01 hcase03 hcase04 hcase12 hcase30 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43
                    omega
                  ·
                    rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
                    ·
                      rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                      ·
                        clear hn4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut63 hcut73 hcut9 hcut19 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase021a hcase111a hcase140b hcase130b hcase101a hcase331a hcase001a hcase300b hcase340b hcase01 hcase03 hcase04 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43
                        omega
                      ·
                        clear hn4 hcut49 hcut16 hcut23 hcut46 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase021a hcase111a hcase140b hcase130b hcase101a hcase331a hcase001a hcase300a hcase300b hcase341a hcase01 hcase03 hcase04 hcase12 hcase31 hcase40 hcase41 hcase42 hcase43
                        omega
                    ·
                      clear hn4 hcut49 hcut16 hcut23 hcut46 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase021a hcase111a hcase140b hcase130b hcase101a hcase331a hcase001a hcase301a hcase01 hcase03 hcase04 hcase12 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43
                      omega
            ·
              rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
              ·
                rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                ·
                  rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase111a hcase111b hcase140a hcase140b hcase131a hcase131b hcase410a hcase410b hcase420a hcase420b hcase030a hcase030b hcase330b hcase00 hcase01 hcase04 hcase10 hcase12 hcase30 hcase31 hcase34 hcase40 hcase43
                      omega
                    ·
                      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase021a hcase021b hcase111a hcase140a hcase140b hcase131a hcase410a hcase410b hcase420a hcase420b hcase030a hcase030b hcase331a hcase331b hcase000b hcase01 hcase04 hcase10 hcase12 hcase30 hcase31 hcase34 hcase40 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase021a hcase111a hcase111b hcase140a hcase140b hcase131a hcase131b hcase410b hcase420b hcase030b hcase331a hcase001a hcase01 hcase04 hcase10 hcase12 hcase30 hcase31 hcase34 hcase40 hcase43
                        omega
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase021a hcase021b hcase111a hcase140a hcase140b hcase131a hcase410a hcase410b hcase420a hcase420b hcase031a hcase031b hcase000b hcase01 hcase04 hcase10 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase43
                      omega
                    ·
                      rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase111a hcase111b hcase140a hcase140b hcase131a hcase131b hcase410a hcase410b hcase420a hcase420b hcase001a hcase001b hcase330b hcase01 hcase04 hcase10 hcase12 hcase30 hcase31 hcase34 hcase40 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hsum_nat3 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase021a hcase111a hcase111b hcase140a hcase140b hcase131a hcase131b hcase410a hcase410b hcase420a hcase420b hcase031a hcase001a hcase331a hcase01 hcase04 hcase10 hcase12 hcase30 hcase31 hcase34 hcase40 hcase43
                        omega
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase021a hcase021b hcase111a hcase140a hcase140b hcase131a hcase410a hcase410b hcase421a hcase421b hcase000b hcase01 hcase03 hcase04 hcase10 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase43
                    omega
                  ·
                    rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase021a hcase021b hcase111a hcase111b hcase140a hcase140b hcase131a hcase131b hcase410a hcase410b hcase421a hcase421b hcase001a hcase001b hcase330b hcase01 hcase03 hcase04 hcase10 hcase12 hcase30 hcase31 hcase34 hcase40 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hsum_nat3 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase021a hcase111a hcase111b hcase140a hcase140b hcase131a hcase131b hcase410a hcase410b hcase421a hcase001a hcase331a hcase01 hcase03 hcase04 hcase10 hcase12 hcase30 hcase31 hcase34 hcase40 hcase43
                      omega
              ·
                rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase021a hcase021b hcase111a hcase140a hcase140b hcase131a hcase411a hcase411b hcase000b hcase01 hcase03 hcase04 hcase10 hcase12 hcase30 hcase31 hcase33 hcase34 hcase40 hcase42 hcase43
                  omega
                ·
                  rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase021a hcase021b hcase111a hcase111b hcase140a hcase140b hcase131a hcase131b hcase411a hcase411b hcase001a hcase001b hcase330b hcase01 hcase03 hcase04 hcase10 hcase12 hcase30 hcase31 hcase34 hcase40 hcase42 hcase43
                    omega
                  ·
                    clear hn4 hsum_nat1 hsum_nat3 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase021a hcase111a hcase111b hcase140a hcase140b hcase131a hcase131b hcase411a hcase001a hcase331a hcase01 hcase03 hcase04 hcase10 hcase12 hcase30 hcase31 hcase34 hcase40 hcase42 hcase43
                    omega
          ·
            rcases hcase10 with ⟨hcase100a, hcase100b⟩ | ⟨hcase101a, hcase101b⟩
            ·
              clear hn4 hsum_nat0 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase021a hcase021b hcase111a hcase141a hcase100b hcase00 hcase01 hcase03 hcase04 hcase12 hcase13 hcase30 hcase31 hcase33 hcase34 hcase40 hcase41 hcase42 hcase43
              omega
            ·
              rcases hcase30 with ⟨hcase300a, hcase300b⟩ | ⟨hcase301a, hcase301b⟩
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase021a hcase021b hcase111a hcase111b hcase141a hcase141b hcase101a hcase101b hcase300a hcase300b hcase330b hcase00 hcase01 hcase03 hcase04 hcase12 hcase13 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43
                  omega
                ·
                  rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                  ·
                    clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase021a hcase021b hcase111a hcase111b hcase141a hcase141b hcase300a hcase300b hcase331a hcase331b hcase000b hcase01 hcase03 hcase04 hcase12 hcase13 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43
                    omega
                  ·
                    rcases hcase34 with ⟨hcase340a, hcase340b⟩ | ⟨hcase341a, hcase341b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310b hcase321a hcase441a hcase441b hcase021a hcase021b hcase111a hcase111b hcase141a hcase141b hcase300b hcase331a hcase001a hcase340b hcase01 hcase03 hcase04 hcase12 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut49 hcut0 hcut23 hcut46 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut42 hcut61 hcut15 hcut36 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430b hcase121a hcase010a hcase010b hcase310b hcase321a hcase441a hcase021a hcase111a hcase111b hcase141a hcase141b hcase300b hcase331a hcase001a hcase341a hcase01 hcase03 hcase04 hcase12 hcase13 hcase31 hcase40 hcase41 hcase42 hcase43
                      omega
              ·
                rcases hcase33 with ⟨hcase330a, hcase330b⟩ | ⟨hcase331a, hcase331b⟩
                ·
                  clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase441b hcase111a hcase111b hcase141a hcase141b hcase101a hcase101b hcase301a hcase301b hcase330b hcase00 hcase01 hcase03 hcase04 hcase12 hcase13 hcase31 hcase34 hcase40 hcase41 hcase42 hcase43
                  omega
                ·
                  rcases hcase41 with ⟨hcase410a, hcase410b⟩ | ⟨hcase411a, hcase411b⟩
                  ·
                    rcases hcase42 with ⟨hcase420a, hcase420b⟩ | ⟨hcase421a, hcase421b⟩
                    ·
                      rcases hcase03 with ⟨hcase030a, hcase030b⟩ | ⟨hcase031a, hcase031b⟩
                      ·
                        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase021a hcase021b hcase111a hcase111b hcase141a hcase141b hcase301a hcase301b hcase331a hcase331b hcase410a hcase410b hcase420a hcase420b hcase030a hcase030b hcase000b hcase01 hcase04 hcase12 hcase13 hcase31 hcase34 hcase40 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat1 hsum_nat3 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase321a hcase321b hcase441a hcase021a hcase111a hcase111b hcase141a hcase141b hcase101a hcase101b hcase301a hcase301b hcase331a hcase410b hcase420b hcase030b hcase001a hcase01 hcase04 hcase12 hcase13 hcase31 hcase34 hcase40 hcase43
                          omega
                      ·
                        rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                        ·
                          clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase021a hcase021b hcase111a hcase111b hcase141a hcase141b hcase301a hcase301b hcase331a hcase331b hcase410a hcase410b hcase420a hcase420b hcase031a hcase031b hcase000b hcase01 hcase04 hcase12 hcase13 hcase31 hcase34 hcase40 hcase43
                          omega
                        ·
                          clear hn4 hsum_nat1 hcut49 hcut16 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase321a hcase441a hcase021a hcase111a hcase141a hcase141b hcase101a hcase101b hcase301a hcase331a hcase410a hcase410b hcase420a hcase420b hcase031a hcase001a hcase01 hcase04 hcase12 hcase13 hcase31 hcase34 hcase40 hcase43
                          omega
                    ·
                      rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                      ·
                        clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase021a hcase021b hcase111a hcase111b hcase141a hcase141b hcase301a hcase301b hcase331a hcase331b hcase410a hcase410b hcase421a hcase421b hcase000b hcase01 hcase03 hcase04 hcase12 hcase13 hcase31 hcase34 hcase40 hcase43
                        omega
                      ·
                        clear hn4 hsum_nat1 hcut49 hcut16 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase321a hcase441a hcase021a hcase111a hcase141a hcase141b hcase101a hcase101b hcase301a hcase331a hcase410a hcase410b hcase421a hcase001a hcase01 hcase03 hcase04 hcase12 hcase13 hcase31 hcase34 hcase40 hcase43
                        omega
                  ·
                    rcases hcase00 with ⟨hcase000a, hcase000b⟩ | ⟨hcase001a, hcase001b⟩
                    ·
                      clear hn4 hsum_nat0 hsum_nat1 hsum_nat3 hsum_nat4 hcut49 hcut16 hcut0 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut5 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut4 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase041b hcase401a hcase401b hcase430a hcase430b hcase121a hcase121b hcase010a hcase010b hcase310a hcase310b hcase441a hcase441b hcase021a hcase021b hcase111a hcase111b hcase141a hcase141b hcase301a hcase301b hcase331a hcase331b hcase411a hcase411b hcase000b hcase01 hcase03 hcase04 hcase12 hcase13 hcase31 hcase34 hcase40 hcase42 hcase43
                      omega
                    ·
                      clear hn4 hsum_nat1 hcut49 hcut16 hcut23 hcut46 hcut67 hcut8 hcut31 hcut29 hcut39 hcut54 hcut62 hcut52 hcut3 hcut42 hcut61 hcut15 hcut36 hcut68 hcut63 hcut73 hcut9 hcut19 hcut69 hcut56 hcut65 hcut44 hu00b hu00c hu01b hu01c hu02b hu02c hu03b hu03c hu04b hu04c hu10b hu10c hu11b hu11c hu12b hu12c hu13b hu13c hu14b hu14c hu30b hu30c hu31b hu31c hu32b hu32c hu33b hu33c hu34b hu34c hu40b hu40c hu41b hu41c hu42b hu42c hu43b hu43c hu44b hu44c hcase041a hcase401a hcase430a hcase430b hcase121a hcase121b hcase010b hcase310a hcase310b hcase321a hcase441a hcase021a hcase111a hcase141a hcase141b hcase101a hcase101b hcase301a hcase331a hcase411a hcase001a hcase01 hcase03 hcase04 hcase12 hcase13 hcase31 hcase34 hcase40 hcase42 hcase43
                      omega

#print axioms symbolic_mask202_integer_shard003
end Jsp404.SixExactFloorKernel
