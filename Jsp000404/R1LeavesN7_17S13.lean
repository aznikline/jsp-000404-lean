import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_17S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8188 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8818 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8819 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8820 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8821 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h0 := hg0
  have h6421 := hg6421
  have h7464 := hg7464
  rcases m.htr 0 3 5 (by decide) (by decide) with h9339 | h9339
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9340 | h9340
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9341 | h9341
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9342 | h9342
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9343 | h9343
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9344 | h9344
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9345 | h9345
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9346 | h9346
                · linarith only [h8818, h8821, h9339, h9346, hc02, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9348 | h9348
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9349 | h9349
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9350 | h9350
                      · rcases h0bigk with h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c | h9351c
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [hlam, p9351_0]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h0, hlam, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h6421, hlam, p9351_0]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h7464, hlam, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h8188, hlam, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [hlam, p9351_0]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h0, h8818, h9348, h9350, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h0, h8818, h8821, h9348, h9350, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h8821, h9344, hc01, hc13, hlam, hphi, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h8818, hlam, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [hlam, p9351_0]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h8821, hlam, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h8188, h8821, h9344, hc01, hc13, hlam, hphi, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h7464, hc01, hc14, hlam, hphi, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h8819, hlam, p9351_0]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h8821, h9344, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [hlam, p9351_0]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h8188, h8821, h9344, hc01, hc13, hlam, hphi, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h8188, h9345, hc01, hc14, hlam, hphi, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h8820, hlam, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h9339, hlam, p9351_0]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [h9340, hlam, p9351_1]
                        · have p9351_0 := h9351c.1
                          have p9351_1 := h9351c.2.1
                          have p9351_2 := h9351c.2.2.1
                          have p9351_3 := h9351c.2.2.2
                          linarith only [hlam, p9351_0]
                      · linarith only [h8821, h9340, h9350, hlam]
                    · linarith only [h8821, h9339, h9340, h9341, h9344, h9346, h9348, h9349, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h8821, h9339, h9341, h9344, h9348, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h7464, h8821, h9339, h9340, h9341, h9344, h9345, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9381 | h9381
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9382 | h9382
                · linarith only [h6421, h9344, h9382, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9384 | h9384
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9385 | h9385
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9386 | h9386
                      · rcases h0bigk with h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c | h9387c
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [hlam, p9387_0]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h0, hlam, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h6421, hlam, p9387_0]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h7464, hlam, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h8188, hlam, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [hlam, p9387_0]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h0, h8818, h9384, h9386, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h0, h7464, hc01, hc12, hlam, hphi, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h6421, hc01, hc13, hlam, hphi, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h8818, hlam, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [hlam, p9387_0]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h8821, hlam, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h6421, h8188, h9344, hc01, hc34, hlam, hphi, ht12, ht23, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h7464, hc01, hc14, hlam, hphi, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h8819, hlam, p9387_0]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h8821, hc03, hc34, hlam, hphi, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [hlam, p9387_0]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h8188, h8821, hc01, hc34, hlam, hphi, ht12, ht23, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h8188, h9381, hc01, hc14, hlam, hphi, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h8820, hlam, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h9339, hlam, p9387_0]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [h9340, hlam, p9387_1]
                        · have p9387_0 := h9387c.1
                          have p9387_1 := h9387c.2.1
                          have p9387_2 := h9387c.2.2.1
                          have p9387_3 := h9387c.2.2.2
                          linarith only [hlam, p9387_0]
                      · linarith only [h6421, h9344, h9386, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h9382, h9384, h9385, hlam]
                  · linarith only [h6421, h9339, h9344, h9384, hc23, hc34, hlam, hphi]
              · linarith only [h6421, h7464, h9339, h9340, h9344, h9381, hc01, hc34, hlam, hphi, ht12, ht23]
          · linarith only [h0, h8820, h9343, hlam]
        · linarith only [h0, h8819, h9342, hlam]
      · linarith only [h0, h8818, h9341, hlam]
    · linarith only [h8821, h9339, h9340, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9421 | h9421
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9422 | h9422
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9423 | h9423
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9424 | h9424
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9425 | h9425
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9426 | h9426
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9427 | h9427
                · linarith only [h8818, h8821, h9427, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9429 | h9429
                  · linarith only [h8818, h9339, h9429, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9431 | h9431
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9432 | h9432
                      · rcases h0bigk with h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c | h9433c
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [hlam, p9433_0]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h0, hlam, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h6421, hlam, p9433_0]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h7464, hlam, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h8188, hlam, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [hlam, p9433_0]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h0, h8819, h9431, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h9339, h9425, h9432, hc01, hc13, hlam, hphi, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h8818, hlam, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [hlam, p9433_0]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h8821, hlam, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h9339, hlam, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h7464, hc01, hc14, hlam, hphi, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h8819, hlam, p9433_0]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h8821, h9425, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [hlam, p9433_0]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h6421, h8821, h9339, h9425, hc01, hc13, hlam, hphi, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h8188, h9426, hc01, hc14, hlam, hphi, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h8820, hlam, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h6421, h9339, h9425, h9432, hc01, hc13, hlam, hphi, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [h9421, hlam, p9433_1]
                        · have p9433_0 := h9433c.1
                          have p9433_1 := h9433c.2.1
                          have p9433_2 := h9433c.2.2.1
                          have p9433_3 := h9433c.2.2.2
                          linarith only [hlam, p9433_0]
                      · linarith only [h8821, h9421, h9432, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9460 | h9460
                      · rcases h0bigk with h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c | h9461c
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [hlam, p9461_0]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h0, hlam, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h6421, hlam, p9461_0]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h7464, hlam, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h8188, hlam, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [hlam, p9461_0]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h0, h9421, h9427, h9431, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h6421, hc01, hc13, hlam, hphi, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h8818, hlam, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [hlam, p9461_0]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h8821, hlam, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h9339, hlam, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h8821, hc01, hc34, hlam, hphi, ht12, ht23, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h8819, hlam, p9461_0]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h8821, hc03, hc34, hlam, hphi, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [hlam, p9461_0]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h6421, h8821, h9339, hc01, hc34, hlam, hphi, ht12, ht23, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h8188, h9425, h9426, hc01, hc13, hlam, hphi, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h8820, hlam, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h6421, h8188, h9425, h9426, hc01, hc13, hlam, hphi, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [h9421, hlam, p9461_1]
                        · have p9461_0 := h9461c.1
                          have p9461_1 := h9461c.2.1
                          have p9461_2 := h9461c.2.2.1
                          have p9461_3 := h9461c.2.2.2
                          linarith only [hlam, p9461_0]
                      · linarith only [h8821, h9421, h9460, hlam]
              · linarith only [h7464, h8821, h9421, h9422, h9425, h9426, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9489 | h9489
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9490 | h9490
                · linarith only [h6421, h9425, h9490, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9492 | h9492
                  · linarith only [h8818, h9339, h9492, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9494 | h9494
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9495 | h9495
                      · rcases h0bigk with h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c | h9496c
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [hlam, p9496_0]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h0, hlam, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h6421, hlam, p9496_0]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h7464, hlam, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h8188, hlam, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [hlam, p9496_0]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h0, h8819, h9494, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h0, h6421, h9339, hc01, hc12, hlam, hphi, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h9339, hc01, hc35, hlam, hphi, ht12, ht23, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h8818, hlam, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [hlam, p9496_0]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h8821, hlam, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h9339, hlam, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h7464, hc01, hc14, hlam, hphi, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h8819, hlam, p9496_0]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h8821, hc03, hc34, hlam, hphi, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [hlam, p9496_0]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h6421, h8821, h9339, hc01, hc34, hlam, hphi, ht12, ht23, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h8188, hc01, hc15, hlam, hphi, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h8820, hlam, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h6421, h9339, hc01, hc35, hlam, hphi, ht12, ht23, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [h9421, hlam, p9496_1]
                        · have p9496_0 := h9496c.1
                          have p9496_1 := h9496c.2.1
                          have p9496_2 := h9496c.2.2.1
                          have p9496_3 := h9496c.2.2.2
                          linarith only [hlam, p9496_0]
                      · linarith only [h6421, h9425, h9494, h9495, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9523 | h9523
                      · rcases h0bigk with h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c | h9524c
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [hlam, p9524_0]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h0, hlam, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h6421, hlam, p9524_0]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h7464, hlam, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h8188, hlam, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [hlam, p9524_0]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h0, h9421, h9490, h9494, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h6421, hc01, hc13, hlam, hphi, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h8818, hlam, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [hlam, p9524_0]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h8821, hlam, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h9339, hlam, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h7464, hc01, hc14, hlam, hphi, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h8819, hlam, p9524_0]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h8821, hc03, hc34, hlam, hphi, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [hlam, p9524_0]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h8188, h8821, hc01, hc34, hlam, hphi, ht12, ht23, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h8188, hc01, hc15, hlam, hphi, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h8820, hlam, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h6421, h9339, h9523, hc01, hc34, hlam, hphi, ht12, ht23, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [h9421, hlam, p9524_1]
                        · have p9524_0 := h9524c.1
                          have p9524_1 := h9524c.2.1
                          have p9524_2 := h9524c.2.2.1
                          have p9524_3 := h9524c.2.2.2
                          linarith only [hlam, p9524_0]
                      · linarith only [h6421, h9425, h9523, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h7464, h9421, h9489, hlam]
          · linarith only [h0, h8819, h8820, h9421, h9424, hlam]
        · linarith only [h0, h8819, h9423, hlam]
      · linarith only [h0, h8818, h9422, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9555 | h9555
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9556 | h9556
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9557 | h9557
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9558 | h9558
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9559 | h9559
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9560 | h9560
                · linarith only [h8818, h8821, h9560, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9562 | h9562
                  · linarith only [h8818, h9339, h9562, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9564 | h9564
                    · linarith only [h8819, h9421, h9564, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9566 | h9566
                      · linarith only [h6421, h8821, h9421, h9555, h9558, h9566, hc01, hc12, hlam, hphi]
                      · linarith only [h6421, h8821, h9559, h9566, hc01, hc14, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9569 | h9569
                · linarith only [h8818, h8821, h9569, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9571 | h9571
                  · linarith only [h8818, h9339, h9571, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9573 | h9573
                    · linarith only [h7464, h9559, h9573, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9575 | h9575
                      · linarith only [h6421, h8821, h9421, h9555, h9558, h9575, hc01, hc12, hlam, hphi]
                      · rcases h0bigk with h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c | h9577c
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [hlam, p9577_0]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h0, hlam, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h6421, hlam, p9577_0]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h7464, hlam, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h8188, hlam, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [hlam, p9577_0]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h0, h6421, h8821, hc01, hc12, hlam, hphi, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h8821, h9558, hc01, hc14, hlam, hphi, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h8818, hlam, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [hlam, p9577_0]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h8821, hlam, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h9339, hlam, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h7464, h9559, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h8819, hlam, p9577_0]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h8821, h9558, h9559, hc03, hc45, hlam, hphi, ht34, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [hlam, p9577_0]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h9421, hlam, p9577_0]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h9339, hc01, hc35, hlam, hphi, ht12, ht23, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h8820, hlam, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h6421, h9339, hc01, hc35, hlam, hphi, ht12, ht23, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [h9421, hc04, hc45, hlam, hphi, p9577_1]
                        · have p9577_0 := h9577c.1
                          have p9577_1 := h9577c.2.1
                          have p9577_2 := h9577c.2.2.1
                          have p9577_3 := h9577c.2.2.2
                          linarith only [hlam, p9577_0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9603 | h9603
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9604 | h9604
                · linarith only [h6421, h9558, h9604, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9606 | h9606
                  · linarith only [h8818, h9339, h9606, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9608 | h9608
                    · linarith only [h0, h6421, h8819, h8821, h9421, h9608, hc01, hc12, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9610 | h9610
                      · rcases h0bigk with h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c | h9611c
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [hlam, p9611_0]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h0, hlam, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h6421, hlam, p9611_0]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h7464, hlam, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h8188, hlam, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [hlam, p9611_0]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h0, h6421, h8821, hc01, hc12, hlam, hphi, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h8821, h9421, h9603, hc01, hc14, hlam, hphi, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h8818, hlam, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [hlam, p9611_0]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h8821, hlam, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h9339, hlam, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h9421, h9558, h9603, hc01, hc34, hlam, hphi, ht12, ht23, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h8819, hlam, p9611_0]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h9421, h9558, h9603, hc03, hc34, hlam, hphi, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [hlam, p9611_0]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h9421, hlam, p9611_0]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h8188, h9558, h9603, hc01, hc34, hlam, hphi, ht12, ht23, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h8820, hlam, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h6421, h8188, h9558, h9603, hc01, hc34, hlam, hphi, ht12, ht23, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [h9421, h9558, h9603, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p9611_1]
                        · have p9611_0 := h9611c.1
                          have p9611_1 := h9611c.2.1
                          have p9611_2 := h9611c.2.2.1
                          have p9611_3 := h9611c.2.2.2
                          linarith only [hlam, p9611_0]
                      · linarith only [h9558, h9603, h9610, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9638 | h9638
                · linarith only [h8818, h8821, h9638, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9640 | h9640
                  · linarith only [h8818, h9339, h9640, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9642 | h9642
                    · linarith only [h7464, h9603, h9642, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9644 | h9644
                      · linarith only [h7464, h9603, h9644, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h6421, h9558, h9644, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h8820, h9557, hlam]
        · linarith only [h0, h8819, h9556, hlam]
      · linarith only [h0, h8818, h9555, hlam]

set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8188 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8818 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8819 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8820 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h0 := hg0
  have h6421 := hg6421
  have h7464 := hg7464
  rcases m.htr 0 3 4 (by decide) (by decide) with h8821 | h8821
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x0_x0_x0_x0 m hb0 hb2 hb4 hg0 hg6421 hg7464 h8188 h8818 h8819 h8820 h8821
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x0_x0_x0_x1 m hb0 hb2 hb4 hg0 hg6421 hg7464 h8188 h8818 h8819 h8820 h8821

set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8188 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8818 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8819 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8820 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h0 := hg0
  have h6421 := hg6421
  have h7464 := hg7464
  rcases m.htr 0 3 4 (by decide) (by decide) with h9650 | h9650
  · rcases m.htr 0 3 5 (by decide) (by decide) with h9651 | h9651
    · linarith only [h8818, h8820, h9651, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9653 | h9653
      · linarith only [h8818, h8820, h9650, h9653, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9655 | h9655
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9656 | h9656
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9657 | h9657
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9658 | h9658
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9659 | h9659
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9660 | h9660
                  · linarith only [h8818, h8820, h9657, h9660, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h8818, h8820, h9650, h9657, h9660, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9663 | h9663
                  · linarith only [h8818, h8820, h9657, h9663, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h8818, h8820, h9650, h9657, h9663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h8818, h8820, h9650, h9657, h9658, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9667 | h9667
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9668 | h9668
                · linarith only [h7464, h9653, h9655, h9657, h9667, h9668, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9670 | h9670
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9671 | h9671
                    · linarith only [h8818, h8820, h9651, h9671, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9673 | h9673
                      · linarith only [h7464, h9668, h9673, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h8818, h9657, h9670, h9673, hc34, hc45, hlam, hphi]
                  · linarith only [h9650, h9651, h9670, hc23, hc35, hlam, hphi]
              · linarith only [h6421, h9650, h9667, hlam]
          · linarith only [h0, h8819, h9656, hlam]
        · linarith only [h0, h8818, h9655, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h9680 | h9680
    · linarith only [h8818, h8820, h9680, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9682 | h9682
      · linarith only [h8819, h8820, h9682, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9684 | h9684
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9685 | h9685
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9686 | h9686
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9687 | h9687
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9688 | h9688
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9689 | h9689
                  · linarith only [h0, h6421, h8818, h9650, h9689, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9691 | h9691
                    · linarith only [h6421, h8819, h8820, h9680, h9686, h9689, h9691, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9693 | h9693
                      · linarith only [h8819, h8820, h9682, h9686, h9693, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9695 | h9695
                        · linarith only [h8819, h8820, h9689, h9693, h9695, hc23, hc34, hlam, hphi]
                        · linarith only [h6421, h9650, h9684, h9687, h9688, h9695, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9698 | h9698
                  · linarith only [h6421, h8818, h8820, h9650, h9698, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9700 | h9700
                    · linarith only [h8819, h8820, h9686, h9698, h9700, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9702 | h9702
                      · linarith only [h8819, h8820, h9686, h9688, h9702, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9704 | h9704
                        · linarith only [h9687, h9688, h9704, hlam]
                        · rcases h0bigk with h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c | h9706c
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [hlam, p9706_0]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h0, hlam, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h6421, hlam, p9706_0]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h7464, hlam, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h8188, hlam, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h8820, h9686, hc01, hc12, hlam, hphi, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [hlam, p9706_0]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h6421, h8820, h9686, hc01, hc12, hlam, hphi, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h6421, h8820, h9650, h9686, hc01, hc12, hlam, hphi, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h8820, hlam, p9706_0]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h9650, h9687, hc01, hc14, hlam, hphi, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h8818, hlam, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [hlam, p9706_0]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h9650, hlam, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h9680, hlam, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h7464, h9688, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h8819, hlam, p9706_0]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h7464, h9688, hc03, hc45, hlam, hphi, ht34, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [hlam, p9706_0]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h9682, hlam, p9706_0]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h8188, hc01, hc15, hlam, hphi, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h8820, h9686, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h6421, h8820, h9686, hc01, hc12, hlam, hphi, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [h8820, h9686, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9706_1]
                          · have p9706_0 := h9706c.1
                            have p9706_1 := h9706c.2.1
                            have p9706_2 := h9706c.2.2.1
                            have p9706_3 := h9706c.2.2.2
                            linarith only [hlam, p9706_0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9732 | h9732
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9733 | h9733
                  · linarith only [h6421, h9687, h9733, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9735 | h9735
                    · linarith only [h8819, h8820, h9686, h9733, h9735, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9737 | h9737
                      · linarith only [h6421, h8819, h8820, h9650, h9682, h9686, h9737, hc01, hc12, hlam, hphi]
                      · linarith only [h8819, h8820, h9687, h9732, h9733, h9737, hc23, hc34, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9740 | h9740
                  · linarith only [h8818, h8820, h9686, h9740, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9742 | h9742
                    · linarith only [h8819, h8820, h9680, h9686, h9740, h9742, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9744 | h9744
                      · linarith only [h8819, h8820, h9686, h9732, h9744, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9746 | h9746
                        · linarith only [h6421, h9687, h9732, h9746, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h6421, h9687, h9746, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9749 | h9749
              · linarith only [h6421, h9650, h9684, h9686, h9749, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9751 | h9751
                · linarith only [h7464, h9682, h9685, h9686, h9751, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9753 | h9753
                  · linarith only [h8818, h9650, h9753, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9755 | h9755
                    · linarith only [h8818, h9680, h9755, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9757 | h9757
                      · linarith only [h0, h8819, h9686, h9751, h9755, h9757, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9759 | h9759
                        · linarith only [h0, h9686, h9757, h9759, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h6421, h9749, h9759, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h8819, h9685, hlam]
        · linarith only [h0, h8818, h9684, hlam]

set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8188 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8818 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8819 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h0 := hg0
  have h6421 := hg6421
  have h7464 := hg7464
  rcases m.htr 0 2 5 (by decide) (by decide) with h8820 | h8820
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x0_x0_x0 m hb0 hb2 hb4 hg0 hg6421 hg7464 h8188 h8818 h8819 h8820
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x0_x0_x1 m hb0 hb2 hb4 hg0 hg6421 hg7464 h8188 h8818 h8819 h8820

end R2N4
