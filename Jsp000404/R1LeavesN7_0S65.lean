import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x4 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 0 1) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 0 1) ∧ (m.d 1 5) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 5) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  rcases p34277_3 (m.d 0 1) (by simp) with h34300 | h34300
  · rcases p34277_3 (m.d 1 2) (by simp) with h34301 | h34301
    · rcases p34277_3 (m.d 1 3) (by simp) with h34302 | h34302
      · linarith only [h33187, h34302, hlam]
      · rcases p34277_3 (m.d 1 4) (by simp) with h34304 | h34304
        · linarith only [h33188, h34304, hlam]
        · rcases p34277_3 (m.d 1 5) (by simp) with h34306 | h34306
          · linarith only [h34306, hlam, p34277_0]
          · rcases h1emax with h34308 | h34308 | h34308 | h34308 | h34308
            · linarith only [h34268, h34308, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p34277_1]
            · linarith only [h0, h34262, h34268, h34270, h34308, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1]
            · rcases h2bigk with h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c | h34311c
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h0, hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                rcases p34311_3 (m.d 0 2) (by simp) with h34314 | h34314
                · rcases p34311_3 (m.d 1 2) (by simp) with h34315 | h34315
                  · rcases p34311_3 (m.d 2 3) (by simp) with h34316 | h34316
                    · linarith only [h34316, hlam, p34311_0]
                    · rcases p34311_3 (m.d 2 4) (by simp) with h34318 | h34318
                      · linarith only [h33191, h34318, hlam]
                      · linarith only [h34270, h34318, hlam]
                  · linarith only [h34261, h34315, hlam]
                · linarith only [h34314, hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                rcases p34311_3 (m.d 0 2) (by simp) with h34323 | h34323
                · rcases p34311_3 (m.d 1 2) (by simp) with h34324 | h34324
                  · rcases p34311_3 (m.d 2 3) (by simp) with h34325 | h34325
                    · linarith only [h33190, h34325, hlam]
                    · rcases p34311_3 (m.d 2 4) (by simp) with h34327 | h34327
                      · linarith only [h34327, hlam, p34311_0]
                      · rcases p34311_3 (m.d 2 5) (by simp) with h34329 | h34329
                        · linarith only [h33192, h34329, hlam]
                        · linarith only [h34274, h34329, hlam]
                  · linarith only [h34262, h34324, hlam]
                · linarith only [h34323, hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                rcases p34311_3 (m.d 0 2) (by simp) with h34334 | h34334
                · rcases p34311_3 (m.d 1 2) (by simp) with h34335 | h34335
                  · rcases p34311_3 (m.d 2 3) (by simp) with h34336 | h34336
                    · linarith only [h33190, h34336, hlam]
                    · rcases p34311_3 (m.d 2 4) (by simp) with h34338 | h34338
                      · linarith only [h33191, h34338, hlam]
                      · rcases p34311_3 (m.d 2 5) (by simp) with h34340 | h34340
                        · linarith only [h34340, hlam, p34311_0]
                        · rcases h4bigk with h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c | h34342c
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [hlam, p34342_0]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h33836, h34262, h34270, h34276, hc23, hc34, hlam, hphi, p34342_1]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h33836, h34270, h34276, hc23, hc34, hlam, hphi, p34342_1]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h33193, hlam, p34342_1]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h33836, hlam, p34342_0]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h33188, hlam, p34342_0]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [hlam, p34342_0]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h34268, h34270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34277_1, p34342_1]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h34264, hlam, p34342_1]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h34268, hlam, p34342_0]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h33191, hlam, p34342_0]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h34262, hlam, p34342_0]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [hlam, p34342_0]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h34270, hlam, p34342_1]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h34274, hlam, p34342_0]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            rcases p34342_3 (m.d 0 4) (by simp) with h34358 | h34358
                            · linarith only [h33193, h34358, hlam]
                            · rcases p34342_3 (m.d 1 4) (by simp) with h34360 | h34360
                              · linarith only [h34264, h34360, hlam]
                              · rcases p34342_3 (m.d 2 4) (by simp) with h34362 | h34362
                                · linarith only [h34270, h34362, hlam]
                                · rcases p34342_3 (m.d 3 4) (by simp) with h34364 | h34364
                                  · rcases p34342_3 (m.d 4 5) (by simp) with h34365 | h34365
                                    · linarith only [h34276, h34365, hlam]
                                    · linarith only [h33836, h34365, hlam]
                                  · linarith only [h33193, h34364, hlam]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            rcases p34342_3 (m.d 0 4) (by simp) with h34369 | h34369
                            · linarith only [h33193, h34369, hlam]
                            · linarith only [h33188, h34369, hlam]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            rcases p34342_3 (m.d 0 4) (by simp) with h34372 | h34372
                            · linarith only [h33193, h34372, hlam]
                            · linarith only [h33191, h34372, hlam]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [hlam, p34342_0]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h33191, h33836, h34270, hc23, hc34, hlam, hphi, p34342_1]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h33187, h33193, h34261, h34276, hc23, hc34, hlam, hphi, p34342_1]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc34, hlam, hphi, p34342_1]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h34270, h34276, hc23, hc34, hlam, hphi, p34342_1]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [h34276, hlam, p34342_0]
                          · have p34342_0 := h34342c.1
                            have p34342_1 := h34342c.2.1
                            have p34342_2 := h34342c.2.2.1
                            have p34342_3 := h34342c.2.2.2
                            linarith only [hlam, p34342_0]
                  · linarith only [h34263, h34335, hlam]
                · linarith only [h34334, hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h0, h34263, h34270, h34274, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34311_1]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h0, h34263, h34270, h34274, hlam, p34277_1, p34311_2]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h0, h34263, h34274, hlam, p34277_1, p34311_2]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h0, h34263, hlam, p34277_1, p34311_2]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h33190, hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h34261, hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h34270, hlam, p34311_1]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h34272, hlam, p34311_1]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h33191, hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h34262, hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h34263, h34274, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34277_1, p34311_1]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h34274, hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h33192, hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h34263, hlam, p34311_0]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h0, h34263, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34311_1]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [h0, h34263, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p34277_1, p34311_1]
              · have p34311_0 := h34311c.1
                have p34311_1 := h34311c.2.1
                have p34311_2 := h34311c.2.2.1
                have p34311_3 := h34311c.2.2.2
                linarith only [hlam, p34311_0]
            · rcases h2bigk with h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c | h34404c
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h0, hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                rcases p34404_3 (m.d 0 2) (by simp) with h34407 | h34407
                · rcases p34404_3 (m.d 1 2) (by simp) with h34408 | h34408
                  · rcases p34404_3 (m.d 2 3) (by simp) with h34409 | h34409
                    · linarith only [h34409, hlam, p34404_0]
                    · rcases p34404_3 (m.d 2 4) (by simp) with h34411 | h34411
                      · linarith only [h33191, h34411, hlam]
                      · linarith only [h34270, h34411, hlam]
                  · linarith only [h34261, h34408, hlam]
                · linarith only [h34407, hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                rcases p34404_3 (m.d 0 2) (by simp) with h34416 | h34416
                · rcases p34404_3 (m.d 1 2) (by simp) with h34417 | h34417
                  · rcases p34404_3 (m.d 2 3) (by simp) with h34418 | h34418
                    · linarith only [h33190, h34418, hlam]
                    · rcases p34404_3 (m.d 2 4) (by simp) with h34420 | h34420
                      · linarith only [h34420, hlam, p34404_0]
                      · rcases p34404_3 (m.d 2 5) (by simp) with h34422 | h34422
                        · linarith only [h33192, h34422, hlam]
                        · linarith only [h34274, h34422, hlam]
                  · linarith only [h34262, h34417, hlam]
                · linarith only [h34416, hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                rcases p34404_3 (m.d 0 2) (by simp) with h34427 | h34427
                · rcases p34404_3 (m.d 1 2) (by simp) with h34428 | h34428
                  · rcases p34404_3 (m.d 2 3) (by simp) with h34429 | h34429
                    · linarith only [h33190, h34429, hlam]
                    · rcases p34404_3 (m.d 2 4) (by simp) with h34431 | h34431
                      · linarith only [h33191, h34431, hlam]
                      · rcases p34404_3 (m.d 2 5) (by simp) with h34433 | h34433
                        · linarith only [h34433, hlam, p34404_0]
                        · rcases h4bigk with h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c | h34435c
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [hlam, p34435_0]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h33836, h34261, h34264, h34276, hc23, hc34, hlam, hphi, p34435_1]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h33836, h34270, h34276, hc23, hc34, hlam, hphi, p34435_1]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h33193, hlam, p34435_1]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h33836, hlam, p34435_0]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h33188, hlam, p34435_0]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [hlam, p34435_0]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34435_1]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h34264, hlam, p34435_1]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h34268, hlam, p34435_0]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h33191, hlam, p34435_0]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h34262, hlam, p34435_0]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [hlam, p34435_0]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h34270, hlam, p34435_1]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h34274, hlam, p34435_0]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            rcases p34435_3 (m.d 0 4) (by simp) with h34451 | h34451
                            · linarith only [h33193, h34451, hlam]
                            · rcases p34435_3 (m.d 1 4) (by simp) with h34453 | h34453
                              · linarith only [h34264, h34453, hlam]
                              · rcases p34435_3 (m.d 2 4) (by simp) with h34455 | h34455
                                · linarith only [h34270, h34455, hlam]
                                · rcases p34435_3 (m.d 3 4) (by simp) with h34457 | h34457
                                  · rcases p34435_3 (m.d 4 5) (by simp) with h34458 | h34458
                                    · linarith only [h34276, h34458, hlam]
                                    · linarith only [h33836, h34458, hlam]
                                  · linarith only [h33193, h34457, hlam]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            rcases p34435_3 (m.d 0 4) (by simp) with h34462 | h34462
                            · linarith only [h33193, h34462, hlam]
                            · linarith only [h33188, h34462, hlam]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            rcases p34435_3 (m.d 0 4) (by simp) with h34465 | h34465
                            · linarith only [h33193, h34465, hlam]
                            · linarith only [h33191, h34465, hlam]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [hlam, p34435_0]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h33191, h33836, h34270, hc23, hc34, hlam, hphi, p34435_1]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h33193, h34276, hc03, hc34, hlam, hphi, p34435_1]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc34, hlam, hphi, p34435_1]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h34270, h34276, hc23, hc34, hlam, hphi, p34435_1]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [h34276, hlam, p34435_0]
                          · have p34435_0 := h34435c.1
                            have p34435_1 := h34435c.2.1
                            have p34435_2 := h34435c.2.2.1
                            have p34435_3 := h34435c.2.2.2
                            linarith only [hlam, p34435_0]
                  · linarith only [h34263, h34428, hlam]
                · linarith only [h34427, hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h0, h34262, h34268, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34404_1]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h0, h34262, h34268, h34270, hlam, p34277_1, p34404_2]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h0, h34262, h34268, hlam, p34277_1, p34404_2]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h0, h34263, hlam, p34277_1, p34404_2]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h33190, hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h34261, hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h34270, hlam, p34404_1]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h34272, hlam, p34404_1]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h33191, hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h34262, hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h34262, h34268, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34277_1, p34404_1]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h34274, hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h33192, hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h34263, hlam, p34404_0]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h0, h34263, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34404_1]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [h0, h34263, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p34277_1, p34404_1]
              · have p34404_0 := h34404c.1
                have p34404_1 := h34404c.2.1
                have p34404_2 := h34404c.2.2.1
                have p34404_3 := h34404c.2.2.2
                linarith only [hlam, p34404_0]
            · rcases h2bigk with h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c | h34497c
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h0, hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                rcases p34497_3 (m.d 0 2) (by simp) with h34500 | h34500
                · rcases p34497_3 (m.d 1 2) (by simp) with h34501 | h34501
                  · rcases p34497_3 (m.d 2 3) (by simp) with h34502 | h34502
                    · linarith only [h34502, hlam, p34497_0]
                    · rcases p34497_3 (m.d 2 4) (by simp) with h34504 | h34504
                      · linarith only [h33191, h34504, hlam]
                      · linarith only [h34270, h34504, hlam]
                  · linarith only [h34261, h34501, hlam]
                · linarith only [h34500, hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                rcases p34497_3 (m.d 0 2) (by simp) with h34509 | h34509
                · rcases p34497_3 (m.d 1 2) (by simp) with h34510 | h34510
                  · rcases p34497_3 (m.d 2 3) (by simp) with h34511 | h34511
                    · linarith only [h33190, h34511, hlam]
                    · rcases p34497_3 (m.d 2 4) (by simp) with h34513 | h34513
                      · linarith only [h34513, hlam, p34497_0]
                      · rcases p34497_3 (m.d 2 5) (by simp) with h34515 | h34515
                        · linarith only [h33192, h34515, hlam]
                        · linarith only [h34274, h34515, hlam]
                  · linarith only [h34262, h34510, hlam]
                · linarith only [h34509, hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                rcases p34497_3 (m.d 0 2) (by simp) with h34520 | h34520
                · rcases p34497_3 (m.d 1 2) (by simp) with h34521 | h34521
                  · rcases p34497_3 (m.d 2 3) (by simp) with h34522 | h34522
                    · linarith only [h33190, h34522, hlam]
                    · rcases p34497_3 (m.d 2 4) (by simp) with h34524 | h34524
                      · linarith only [h33191, h34524, hlam]
                      · rcases p34497_3 (m.d 2 5) (by simp) with h34526 | h34526
                        · linarith only [h34526, hlam, p34497_0]
                        · rcases h4bigk with h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c | h34528c
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [hlam, p34528_0]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h33836, h34276, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p34528_1]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h33836, h34270, h34276, hc23, hc34, hlam, hphi, p34528_1]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h33193, hlam, p34528_1]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h33836, hlam, p34528_0]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h33188, hlam, p34528_0]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [hlam, p34528_0]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34528_1]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h34264, hlam, p34528_1]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h34268, hlam, p34528_0]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h33191, hlam, p34528_0]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h34262, hlam, p34528_0]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [hlam, p34528_0]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h34270, hlam, p34528_1]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h34274, hlam, p34528_0]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            rcases p34528_3 (m.d 0 4) (by simp) with h34544 | h34544
                            · linarith only [h33193, h34544, hlam]
                            · rcases p34528_3 (m.d 1 4) (by simp) with h34546 | h34546
                              · linarith only [h34264, h34546, hlam]
                              · rcases p34528_3 (m.d 2 4) (by simp) with h34548 | h34548
                                · linarith only [h34270, h34548, hlam]
                                · rcases p34528_3 (m.d 3 4) (by simp) with h34550 | h34550
                                  · rcases p34528_3 (m.d 4 5) (by simp) with h34551 | h34551
                                    · linarith only [h34276, h34551, hlam]
                                    · linarith only [h33836, h34551, hlam]
                                  · linarith only [h33193, h34550, hlam]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            rcases p34528_3 (m.d 0 4) (by simp) with h34555 | h34555
                            · linarith only [h33193, h34555, hlam]
                            · linarith only [h33188, h34555, hlam]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            rcases p34528_3 (m.d 0 4) (by simp) with h34558 | h34558
                            · linarith only [h33193, h34558, hlam]
                            · linarith only [h33191, h34558, hlam]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [hlam, p34528_0]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h33191, h33836, h34270, hc23, hc34, hlam, hphi, p34528_1]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h33193, h34276, hc03, hc34, hlam, hphi, p34528_1]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc34, hlam, hphi, p34528_1]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h34270, h34276, hc23, hc34, hlam, hphi, p34528_1]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [h34276, hlam, p34528_0]
                          · have p34528_0 := h34528c.1
                            have p34528_1 := h34528c.2.1
                            have p34528_2 := h34528c.2.2.1
                            have p34528_3 := h34528c.2.2.2
                            linarith only [hlam, p34528_0]
                  · linarith only [h34263, h34521, hlam]
                · linarith only [h34520, hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h0, h34262, h34268, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34497_1]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h0, h34262, h34268, h34270, hlam, p34277_1, p34497_2]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h0, h34262, h34268, hlam, p34277_1, p34497_2]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h0, h34263, hlam, p34277_1, p34497_2]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h33190, hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h34261, hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h34270, hlam, p34497_1]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h34272, hlam, p34497_1]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h33191, hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h34262, hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h34262, h34268, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34277_1, p34497_1]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h34274, hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h33192, hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h34263, hlam, p34497_0]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h0, h34263, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34497_1]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [h0, h34263, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p34277_1, p34497_1]
              · have p34497_0 := h34497c.1
                have p34497_1 := h34497c.2.1
                have p34497_2 := h34497c.2.2.1
                have p34497_3 := h34497c.2.2.2
                linarith only [hlam, p34497_0]
    · linarith only [h34263, h34301, hlam]
  · linarith only [h34300, hlam, p34277_0]

end R2N4
