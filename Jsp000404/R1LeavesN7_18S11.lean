import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h7594 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8272 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8273 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8274 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8275 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 3 5 (by decide) (by decide) with h8276 | h8276
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8277 | h8277
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8278 | h8278
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8279 | h8279
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8280 | h8280
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8281 | h8281
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8282 | h8282
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8283 | h8283
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8284 | h8284
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8285 | h8285
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8286 | h8286
                      · rcases h0bigk with h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [hlam, p8287_0]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h0, hlam, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h5743, hlam, p8287_0]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h6852, hlam, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h7594, hlam, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [hlam, p8287_0]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h0, h8272, h8283, h8286, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h0, h6852, hc01, hc12, hlam, hphi, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h5743, hc01, hc13, hlam, hphi, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h8272, hlam, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [hlam, p8287_0]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h0, h7594, h8272, h8277, hc01, hc12, hlam, hphi, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h0, h7594, h8272, hc01, hc12, hlam, hphi, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h6852, hc01, hc14, hlam, hphi, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h8273, hlam, p8287_0]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h8275, hlam, p8287_0]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [hlam, p8287_0]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h0, h7594, h8272, h8275, hc01, hc12, hlam, hphi, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h7594, hc01, hc15, hlam, hphi, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h8274, hlam, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h8276, hlam, p8287_0]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [h8277, hlam, p8287_1]
                        · have p8287_0 := h8287c.1
                          have p8287_1 := h8287c.2.1
                          have p8287_2 := h8287c.2.2.1
                          have p8287_3 := h8287c.2.2.2
                          linarith only [hlam, p8287_0]
                      · rcases h0bigk with h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [hlam, p8313_0]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h0, hlam, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h5743, hlam, p8313_0]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h6852, hlam, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h7594, hlam, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [hlam, p8313_0]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h0, h7594, h8277, hc01, hc12, hlam, hphi, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h5743, h8278, hc01, hc12, hlam, hphi, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h8272, hlam, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [hlam, p8313_0]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h5743, h8273, h8278, h8285, h8286, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h5743, h7594, h8278, hc01, hc12, hlam, hphi, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h6852, h8278, h8281, hc01, hc12, hlam, hphi, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h8273, hlam, p8313_0]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h8275, hlam, p8313_0]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [hlam, p8313_0]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h6852, h7594, h8278, h8281, hc01, hc12, hlam, hphi, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h7594, h8278, h8282, hc01, hc12, hlam, hphi, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h8274, hlam, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h8276, hlam, p8313_0]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [h8277, hlam, p8313_1]
                        · have p8313_0 := h8313c.1
                          have p8313_1 := h8313c.2.1
                          have p8313_2 := h8313c.2.2.1
                          have p8313_3 := h8313c.2.2.2
                          linarith only [hlam, p8313_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8339 | h8339
                      · linarith only [h0, h8272, h8283, h8285, h8339, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h0bigk with h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c | h8341c
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [hlam, p8341_0]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h0, hlam, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h5743, hlam, p8341_0]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h6852, hlam, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h7594, hlam, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [hlam, p8341_0]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h0, h6852, hc01, hc12, hlam, hphi, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h5743, h8278, hc01, hc12, hlam, hphi, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h8272, hlam, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [hlam, p8341_0]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h5743, h6852, h8278, hc01, hc12, hlam, hphi, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h5743, h7594, h8278, hc01, hc12, hlam, hphi, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h6852, h8278, h8281, hc01, hc12, hlam, hphi, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h8273, hlam, p8341_0]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h8275, hlam, p8341_0]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [hlam, p8341_0]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h6852, h7594, h8278, h8281, hc01, hc12, hlam, hphi, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h7594, h8278, h8282, hc01, hc12, hlam, hphi, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h8274, hlam, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h8276, hlam, p8341_0]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [h8277, hlam, p8341_1]
                        · have p8341_0 := h8341c.1
                          have p8341_1 := h8341c.2.1
                          have p8341_2 := h8341c.2.2.1
                          have p8341_3 := h8341c.2.2.2
                          linarith only [hlam, p8341_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8367 | h8367
                    · linarith only [h8283, h8284, h8367, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8369 | h8369
                      · linarith only [h0, h8272, h8283, h8367, h8369, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h0bigk with h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c | h8371c
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [hlam, p8371_0]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h0, hlam, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h5743, hlam, p8371_0]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h6852, hlam, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h7594, hlam, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [hlam, p8371_0]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h0, h8277, h8284, h8369, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h5743, h8278, hc01, hc12, hlam, hphi, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h8272, hlam, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [hlam, p8371_0]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h5743, h8277, h8278, h8284, h8369, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h5743, h7594, h8278, hc01, hc12, hlam, hphi, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h6852, h8278, h8281, hc01, hc12, hlam, hphi, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h8273, hlam, p8371_0]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h8275, hlam, p8371_0]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [hlam, p8371_0]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h6852, h7594, h8278, h8281, hc01, hc12, hlam, hphi, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h7594, h8278, h8282, hc01, hc12, hlam, hphi, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h8274, hlam, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h8276, hlam, p8371_0]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [h8277, hlam, p8371_1]
                        · have p8371_0 := h8371c.1
                          have p8371_1 := h8371c.2.1
                          have p8371_2 := h8371c.2.2.1
                          have p8371_3 := h8371c.2.2.2
                          linarith only [hlam, p8371_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8397 | h8397
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8398 | h8398
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8399 | h8399
                      · rcases h0bigk with h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c | h8400c
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [hlam, p8400_0]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h0, hlam, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h5743, hlam, p8400_0]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h6852, hlam, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h7594, hlam, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [hlam, p8400_0]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h0, h6852, hc01, hc12, hlam, hphi, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h5743, h8278, hc01, hc12, hlam, hphi, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h8272, hlam, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [hlam, p8400_0]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h5743, h8273, h8278, h8283, h8397, h8399, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h5743, h7594, h8278, hc01, hc12, hlam, hphi, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h6852, h8278, h8281, hc01, hc12, hlam, hphi, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h8273, hlam, p8400_0]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h8275, hlam, p8400_0]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [hlam, p8400_0]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h6852, h7594, h8278, h8281, hc01, hc12, hlam, hphi, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h7594, h8278, h8282, hc01, hc12, hlam, hphi, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h8274, hlam, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h8276, hlam, p8400_0]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [h8277, hlam, p8400_1]
                        · have p8400_0 := h8400c.1
                          have p8400_1 := h8400c.2.1
                          have p8400_2 := h8400c.2.2.1
                          have p8400_3 := h8400c.2.2.2
                          linarith only [hlam, p8400_0]
                      · linarith only [h6852, h8277, h8278, h8281, h8283, h8397, h8399, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h8283, h8397, h8398, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8428 | h8428
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8429 | h8429
                      · rcases h0bigk with h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c | h8430c
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [hlam, p8430_0]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h0, hlam, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h5743, hlam, p8430_0]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h6852, hlam, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h7594, hlam, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [hlam, p8430_0]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h0, h6852, hc01, hc12, hlam, hphi, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h5743, h8278, hc01, hc12, hlam, hphi, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h8272, hlam, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [hlam, p8430_0]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h5743, h8273, h8278, h8428, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h5743, h7594, h8278, hc01, hc12, hlam, hphi, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h6852, h8278, h8281, hc01, hc12, hlam, hphi, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h8273, hlam, p8430_0]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h8275, hlam, p8430_0]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [hlam, p8430_0]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h6852, h8276, h8278, h8281, h8397, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h7594, h8278, h8282, hc01, hc12, hlam, hphi, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h8274, hlam, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h8276, hlam, p8430_0]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [h8277, hlam, p8430_1]
                        · have p8430_0 := h8430c.1
                          have p8430_1 := h8430c.2.1
                          have p8430_2 := h8430c.2.2.1
                          have p8430_3 := h8430c.2.2.2
                          linarith only [hlam, p8430_0]
                      · linarith only [h0, h8273, h8283, h8428, h8429, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8457 | h8457
                      · rcases h0bigk with h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c | h8458c
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [hlam, p8458_0]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h0, hlam, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h5743, hlam, p8458_0]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h6852, hlam, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h7594, hlam, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [hlam, p8458_0]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h0, h8275, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h0, h6852, hc01, hc12, hlam, hphi, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h5743, h8278, hc01, hc12, hlam, hphi, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h8272, hlam, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [hlam, p8458_0]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h5743, h7594, h8277, h8278, hc01, hc12, hlam, hphi, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h5743, h7594, h8278, hc01, hc12, hlam, hphi, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h6852, h8278, h8281, hc01, hc12, hlam, hphi, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h8273, hlam, p8458_0]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h8275, hlam, p8458_0]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [hlam, p8458_0]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h6852, h8276, h8278, h8281, h8283, h8428, h8457, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h7594, h8278, h8282, hc01, hc12, hlam, hphi, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h8274, hlam, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h8276, hlam, p8458_0]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [h8277, hlam, p8458_1]
                        · have p8458_0 := h8458c.1
                          have p8458_1 := h8458c.2.1
                          have p8458_2 := h8458c.2.2.1
                          have p8458_3 := h8458c.2.2.2
                          linarith only [hlam, p8458_0]
                      · rcases h0bigk with h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c | h8484c
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [hlam, p8484_0]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h0, hlam, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h5743, hlam, p8484_0]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h6852, hlam, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h7594, hlam, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [hlam, p8484_0]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h0, h6852, hc01, hc12, hlam, hphi, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h5743, h8278, hc01, hc12, hlam, hphi, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h8272, hlam, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [hlam, p8484_0]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h5743, h7594, h8277, h8278, hc01, hc12, hlam, hphi, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h5743, h7594, h8278, hc01, hc12, hlam, hphi, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h6852, h8278, h8281, hc01, hc12, hlam, hphi, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h8273, hlam, p8484_0]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h8275, hlam, p8484_0]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [hlam, p8484_0]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h6852, h7594, h8278, h8281, hc01, hc12, hlam, hphi, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h7594, h8278, h8282, hc01, hc12, hlam, hphi, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h8274, hlam, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h8276, hlam, p8484_0]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [h8277, hlam, p8484_1]
                        · have p8484_0 := h8484c.1
                          have p8484_1 := h8484c.2.1
                          have p8484_2 := h8484c.2.2.1
                          have p8484_3 := h8484c.2.2.2
                          linarith only [hlam, p8484_0]
              · linarith only [h5743, h8276, h8282, hlam]
            · linarith only [h5743, h8275, h8281, hlam]
          · linarith only [h0, h8274, h8280, hlam]
        · linarith only [h0, h8273, h8279, hlam]
      · linarith only [h0, h8272, h8278, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8515 | h8515
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8516 | h8516
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8517 | h8517
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8518 | h8518
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8519 | h8519
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8520 | h8520
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8521 | h8521
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8522 | h8522
                    · linarith only [h0, h6852, h8272, h8277, h8520, h8522, hc01, hc12, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8524 | h8524
                      · linarith only [h8273, h8277, h8520, h8524, hlam]
                      · rcases h0bigk with h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [hlam, p8526_0]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h0, hlam, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h5743, hlam, p8526_0]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h6852, hlam, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h7594, hlam, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [hlam, p8526_0]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h0, h6852, hc01, hc12, hlam, hphi, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h0, h6852, h8277, hc01, hc12, hlam, hphi, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h5743, hc01, hc13, hlam, hphi, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h8272, hlam, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [hlam, p8526_0]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h0, h6852, h8272, hc01, hc12, hlam, hphi, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h0, h6852, h8272, h8277, hc01, hc12, hlam, hphi, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h8277, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h8273, hlam, p8526_0]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h8275, hlam, p8526_0]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [hlam, p8526_0]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h8277, hlam, p8526_0]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h7594, hc01, hc15, hlam, hphi, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h8274, hlam, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h8276, hlam, p8526_0]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [h8277, hc04, hc45, hlam, hphi, p8526_1]
                        · have p8526_0 := h8526c.1
                          have p8526_1 := h8526c.2.1
                          have p8526_2 := h8526c.2.2.1
                          have p8526_3 := h8526c.2.2.2
                          linarith only [hlam, p8526_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8552 | h8552
                    · linarith only [h8273, h8277, h8552, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8554 | h8554
                      · linarith only [h8272, h8276, h8277, h8520, h8521, h8554, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h0bigk with h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c | h8556c
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [hlam, p8556_0]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h0, hlam, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h5743, hlam, p8556_0]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h6852, hlam, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h7594, hlam, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [hlam, p8556_0]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h0, h8276, h8521, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h0, h6852, hc01, hc12, hlam, hphi, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h5743, h8515, hc01, hc12, hlam, hphi, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h8272, hlam, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [hlam, p8556_0]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h5743, h6852, h8515, hc01, hc12, hlam, hphi, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h5743, h7594, h8515, hc01, hc12, hlam, hphi, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h6852, hc01, hc14, hlam, hphi, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h8273, hlam, p8556_0]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h8275, hlam, p8556_0]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [hlam, p8556_0]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h8277, hlam, p8556_0]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h8277, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h8274, hlam, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h8276, hlam, p8556_0]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [h8277, hc04, hc45, hlam, hphi, p8556_1]
                        · have p8556_0 := h8556c.1
                          have p8556_1 := h8556c.2.1
                          have p8556_2 := h8556c.2.2.1
                          have p8556_3 := h8556c.2.2.2
                          linarith only [hlam, p8556_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8582 | h8582
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8583 | h8583
                    · linarith only [h8275, h8277, h8520, h8582, h8583, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h8520, h8582, h8583, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8586 | h8586
                    · linarith only [h0, h8273, h8275, h8277, h8520, h8586, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8588 | h8588
                      · linarith only [h8275, h8277, h8588, hlam]
                      · rcases h0bigk with h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c | h8590c
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [hlam, p8590_0]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h0, hlam, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h5743, hlam, p8590_0]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h6852, hlam, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h7594, hlam, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [hlam, p8590_0]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h0, h8275, h8520, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h5743, h8515, hc01, hc12, hlam, hphi, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h8272, hlam, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [hlam, p8590_0]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h5743, h8275, h8515, h8520, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h5743, h7594, h8515, hc01, hc12, hlam, hphi, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h8277, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h8273, hlam, p8590_0]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h8275, hlam, p8590_0]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [hlam, p8590_0]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h8277, hlam, p8590_0]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h7594, h8515, h8519, hc01, hc12, hlam, hphi, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h8274, hlam, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h8276, hlam, p8590_0]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [h8277, hc04, hc45, hlam, hphi, p8590_1]
                        · have p8590_0 := h8590c.1
                          have p8590_1 := h8590c.2.1
                          have p8590_2 := h8590c.2.2.1
                          have p8590_3 := h8590c.2.2.2
                          linarith only [hlam, p8590_0]
              · linarith only [h5743, h8276, h8519, hlam]
            · linarith only [h5743, h8275, h8518, hlam]
          · linarith only [h0, h8272, h8274, h8276, h8517, hlam]
        · linarith only [h0, h8273, h8516, hlam]
      · linarith only [h0, h8272, h8515, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8621 | h8621
    · linarith only [h8275, h8276, h8621, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8623 | h8623
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8624 | h8624
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8625 | h8625
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8626 | h8626
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8627 | h8627
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8628 | h8628
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8629 | h8629
                  · linarith only [h0, h5743, h8272, h8276, h8629, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8631 | h8631
                    · linarith only [h0, h6852, h8273, h8621, h8631, hc01, hc12, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8633 | h8633
                      · linarith only [h6852, h8272, h8276, h8621, h8627, h8628, h8633, hc01, hc13, hlam, hphi]
                      · rcases h0bigk with h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c | h8635c
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [hlam, p8635_0]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h0, hlam, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h5743, hlam, p8635_0]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h6852, hlam, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h7594, hlam, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [hlam, p8635_0]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h0, h8272, h8628, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h0, h6852, hc01, hc12, hlam, hphi, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h5743, h8623, hc01, hc12, hlam, hphi, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h8272, hlam, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [hlam, p8635_0]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h5743, h6852, h8623, hc01, hc12, hlam, hphi, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h8276, hlam, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h6852, hc01, hc14, hlam, hphi, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h8273, hlam, p8635_0]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h8275, hlam, p8635_0]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [hlam, p8635_0]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h8621, hlam, p8635_0]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h7594, h8623, h8627, hc01, hc12, hlam, hphi, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h8274, hlam, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h8276, h8623, h8627, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [h6852, h8276, h8623, h8627, hc01, hc12, hlam, hphi, p8635_1]
                        · have p8635_0 := h8635c.1
                          have p8635_1 := h8635c.2.1
                          have p8635_2 := h8635c.2.2.1
                          have p8635_3 := h8635c.2.2.2
                          linarith only [hlam, p8635_0]
                · linarith only [h8275, h8276, h8623, h8627, h8628, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8662 | h8662
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8663 | h8663
                  · linarith only [h0, h7594, h8272, h8627, h8663, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8665 | h8665
                    · linarith only [h8273, h8621, h8665, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8667 | h8667
                      · linarith only [h8272, h8276, h8621, h8662, h8667, hlam]
                      · rcases h0bigk with h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [hlam, p8669_0]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h0, hlam, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h5743, hlam, p8669_0]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h6852, hlam, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h7594, hlam, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [hlam, p8669_0]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h0, h8272, h8662, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h0, h6852, hc01, hc12, hlam, hphi, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h0, h8272, h8276, h8662, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h5743, hc01, hc13, hlam, hphi, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h8272, hlam, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [hlam, p8669_0]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h5743, h6852, h8627, h8667, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h8276, hlam, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h6852, hc01, hc14, hlam, hphi, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h8273, hlam, p8669_0]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h8275, hlam, p8669_0]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [hlam, p8669_0]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h8621, hlam, p8669_0]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h7594, hc01, hc15, hlam, hphi, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h8274, hlam, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h8276, h8667, hc03, hc45, hlam, hphi, ht34, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [h6852, h8276, h8667, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p8669_1]
                        · have p8669_0 := h8669c.1
                          have p8669_1 := h8669c.2.1
                          have p8669_2 := h8669c.2.2.1
                          have p8669_3 := h8669c.2.2.2
                          linarith only [hlam, p8669_0]
                · linarith only [h5743, h8275, h8627, h8662, hc23, hc35, hlam, hphi]
            · linarith only [h5743, h8275, h8626, hlam]
          · linarith only [h0, h8274, h8625, hlam]
        · linarith only [h0, h8273, h8624, hlam]
      · linarith only [h0, h8272, h8623, hlam]

end R2N4
