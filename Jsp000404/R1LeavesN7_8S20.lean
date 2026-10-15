import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11598000 in
set_option maxHeartbeats 11598000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h9886 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14268 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  rcases m.htr 0 2 5 (by decide) (by decide) with h14269 | h14269
  · rcases m.htr 0 3 4 (by decide) (by decide) with h14270 | h14270
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14271 | h14271
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14272 | h14272
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14273 | h14273
          · linarith only [h14269, h14273, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14275 | h14275
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14276 | h14276
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14277 | h14277
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14278 | h14278
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14279 | h14279
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14280 | h14280
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14281 | h14281
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14282 | h14282
                          · linarith only [h0, h14268, h14273, h14282, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14284 | h14284
                            · linarith only [h14280, h14282, h14284, hlam]
                            · rcases h0bigk with h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c | h14286c
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [hlam, p14286_0]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h0, hlam, p14286_1]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h7600, hlam, p14286_0]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h8836, hlam, p14286_1]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h9666, hlam, p14286_1]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h0, h14273, hc01, hc23, hlam, hphi, ht12, p14286_1]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [hlam, p14286_0]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h9886, hlam, p14286_0]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h0, h14272, h14273, h14280, h14282, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14286_1]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h0, h14273, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p14286_1, u5ehi0]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                rcases p14286_3 (m.d 0 1) (by simp) with h14297 | h14297
                                · linarith only [h14297, h7600, hlam]
                                · rcases p14286_3 (m.d 0 2) (by simp) with h14299 | h14299
                                  · linarith only [h14299, h9886, hlam]
                                  · linarith only [h0, h14299, hlam]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h14268, h14272, h14280, h14282, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p14286_1]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [hlam, p14286_0]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h14272, h14280, h14282, h9886, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14286_1]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                rcases p14286_3 (m.d 0 1) (by simp) with h14305 | h14305
                                · linarith only [h14305, h7600, hlam]
                                · rcases p14286_3 (m.d 0 2) (by simp) with h14307 | h14307
                                  · linarith only [h14307, h9886, hlam]
                                  · linarith only [h14269, h14307, hlam]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h0, h14268, h14273, hc01, hc23, hlam, hphi, ht12, p14286_1]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h14268, hlam, p14286_0]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h14270, hlam, p14286_0]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [hlam, p14286_0]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h0, h14268, h14272, h14273, h14280, h14282, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14286_1]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h14273, h14275, h14279, h9666, hc01, hc23, hlam, hphi, ht12, p14286_1]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h14269, hlam, p14286_1]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h14271, hlam, p14286_0]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [h14272, hlam, p14286_1]
                              · have p14286_0 := h14286c.1
                                have p14286_1 := h14286c.2.1
                                have p14286_2 := h14286c.2.2.1
                                have p14286_3 := h14286c.2.2.2
                                linarith only [hlam, p14286_0]
                        · linarith only [h0, h14273, h14281, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h14268, h14272, h14273, h14280, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · linarith only [h0, h14268, h14272, h14279, h8836, hc01, hc12, hlam, hphi]
                  · linarith only [h14269, h14271, h14278, h7600, h9886, hlam]
                · linarith only [h14270, h14277, h7600, hlam]
              · linarith only [h0, h14269, h14276, hlam]
            · linarith only [h0, h14268, h14275, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14327 | h14327
          · linarith only [h14269, h14327, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14329 | h14329
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14330 | h14330
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14331 | h14331
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14332 | h14332
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14333 | h14333
                    · linarith only [h14272, h14327, h14329, h14333, h8836, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14335 | h14335
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14336 | h14336
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14337 | h14337
                          · linarith only [h14333, h14337, h8836, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14339 | h14339
                            · linarith only [h14269, h14333, h14335, h14337, h14339, h8836, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases h0bigk with h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c | h14341c
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [hlam, p14341_0]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h0, hlam, p14341_1]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h7600, hlam, p14341_0]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h8836, hlam, p14341_1]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h9666, hlam, p14341_1]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h0, h14327, hc01, hc23, hlam, hphi, ht12, p14341_1]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [hlam, p14341_0]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h9886, hlam, p14341_0]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h0, h14327, h8836, hc01, hc23, hlam, hphi, ht12, p14341_1]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h0, h14327, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p14341_1, u5ehi0]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                rcases p14341_3 (m.d 0 1) (by simp) with h14352 | h14352
                                · linarith only [h14352, h7600, hlam]
                                · rcases p14341_3 (m.d 0 2) (by simp) with h14354 | h14354
                                  · linarith only [h14354, h9886, hlam]
                                  · linarith only [h0, h14354, hlam]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h14269, h7600, hc13, hlam, hphi, ht01, ht0b, ht5b, p14341_1, u5ehi2]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [hlam, p14341_0]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                rcases p14341_3 (m.d 0 1) (by simp) with h14359 | h14359
                                · linarith only [h14359, h7600, hlam]
                                · rcases p14341_3 (m.d 0 2) (by simp) with h14361 | h14361
                                  · linarith only [h14361, h9886, hlam]
                                  · linarith only [h14268, h14361, hlam]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                rcases p14341_3 (m.d 0 1) (by simp) with h14364 | h14364
                                · linarith only [h14364, h7600, hlam]
                                · rcases p14341_3 (m.d 0 2) (by simp) with h14366 | h14366
                                  · linarith only [h14366, h9886, hlam]
                                  · linarith only [h14269, h14366, hlam]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h14333, h8836, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14341_1]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h14268, hlam, p14341_0]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h14270, hlam, p14341_0]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [hlam, p14341_0]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h14272, hlam, p14341_0]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h14269, h9886, hc01, hc23, hlam, hphi, ht12, p14341_1]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h14269, hlam, p14341_1]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h14271, hlam, p14341_0]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [h14269, h8836, h9886, hc01, hc23, hlam, hphi, ht12, p14341_1]
                              · have p14341_0 := h14341c.1
                                have p14341_1 := h14341c.2.1
                                have p14341_2 := h14341c.2.2.1
                                have p14341_3 := h14341c.2.2.2
                                linarith only [hlam, p14341_0]
                        · linarith only [h0, h14327, h14336, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h14269, h14327, h14335, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h14269, h14271, h14332, h7600, h9886, hlam]
                · linarith only [h14268, h14270, h14331, h7600, h9886, hlam]
              · linarith only [h0, h14269, h14330, hlam]
            · linarith only [h0, h14268, h14329, hlam]
      · linarith only [h14269, h14271, h9886, hlam]
    · linarith only [h14268, h14270, h9886, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h14387 | h14387
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14388 | h14388
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14389 | h14389
        · linarith only [h14268, h14269, h14389, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14391 | h14391
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14392 | h14392
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14393 | h14393
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14394 | h14394
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14395 | h14395
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14396 | h14396
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14397 | h14397
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14398 | h14398
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14399 | h14399
                          · linarith only [h14268, h14269, h14389, h14393, h14399, h8836, hc01, hc15, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14401 | h14401
                            · linarith only [h14268, h14269, h14397, h14399, h14401, hlam]
                            · rcases h0bigk with h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c | h14403c
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [hlam, p14403_0]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h0, hlam, p14403_1]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h7600, hlam, p14403_0]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h8836, hlam, p14403_1]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h9666, hlam, p14403_1]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h14269, h14394, h14396, h14399, hc01, hc13, hlam, hphi, p14403_1]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [hlam, p14403_0]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h9886, hlam, p14403_0]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h14269, h14394, h14396, h14399, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p14403_1]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h14269, hlam, p14403_0]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h14391, h9886, hc01, hc12, hlam, hphi, p14403_1]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h14268, h14391, h9886, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p14403_1]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [hlam, p14403_0]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h14391, h8836, h9886, hc01, hc12, hlam, hphi, p14403_1]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h14391, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, p14403_1, u5ehi0]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h14268, h14391, h9886, hc01, hc12, hlam, hphi, p14403_1]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h14268, hlam, p14403_0]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h14387, hlam, p14403_0]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [hlam, p14403_0]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h14389, hlam, p14403_0]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h14269, h14394, h14396, h14399, hc01, hc13, hlam, hphi, p14403_1]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h0, h14269, h14394, h14396, h14399, hc01, hc13, hlam, hphi, p14403_1]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h14388, hlam, p14403_0]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [h14269, h14394, h14396, h14399, h8836, hc01, hc13, hlam, hphi, p14403_1]
                              · have p14403_0 := h14403c.1
                                have p14403_1 := h14403c.2.1
                                have p14403_2 := h14403c.2.2.1
                                have p14403_3 := h14403c.2.2.2
                                linarith only [hlam, p14403_0]
                        · linarith only [h14388, h14398, h9886, hlam]
                      · linarith only [h14387, h14397, h9886, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14431 | h14431
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14432 | h14432
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14433 | h14433
                          · linarith only [h14268, h14269, h14396, h14432, h14433, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14435 | h14435
                            · linarith only [h14396, h14435, h8836, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c | h14437c
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [hlam, p14437_0]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h0, hlam, p14437_1]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h7600, hlam, p14437_0]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h8836, hlam, p14437_1]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h9666, hlam, p14437_1]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h14269, h14391, h14432, hc01, hc12, hlam, hphi, p14437_1]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [hlam, p14437_0]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h9886, hlam, p14437_0]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h14269, h14391, h14432, h8836, hc01, hc12, hlam, hphi, p14437_1]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h14269, hlam, p14437_0]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h14391, h9886, hc01, hc12, hlam, hphi, p14437_1]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h14268, h14391, h9886, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p14437_1]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [hlam, p14437_0]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h14391, h8836, h9886, hc01, hc12, hlam, hphi, p14437_1]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h14391, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, p14437_1, u5ehi0]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h14396, h8836, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14437_1]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h14268, hlam, p14437_0]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h14387, hlam, p14437_0]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [hlam, p14437_0]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h14389, hlam, p14437_0]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h14269, h14391, h14432, hc01, hc12, hlam, hphi, p14437_1]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h0, h14269, h14391, h14432, hc01, hc12, hlam, hphi, p14437_1]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h14388, hlam, p14437_0]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [h14269, h14391, h14432, h8836, hc01, hc12, hlam, hphi, p14437_1]
                              · have p14437_0 := h14437c.1
                                have p14437_1 := h14437c.2.1
                                have p14437_2 := h14437c.2.2.1
                                have p14437_3 := h14437c.2.2.2
                                linarith only [hlam, p14437_0]
                        · linarith only [h14388, h14432, h9886, hlam]
                      · linarith only [h14387, h14431, h9886, hlam]
                  · linarith only [h14388, h14395, h7600, h9886, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h14268, h14387, h14391, h14394, h9886, hlam]
              · linarith only [h14268, h14391, h14393, h9886, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h14268, h14391, h14392, h9886, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14469 | h14469
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14470 | h14470
              · linarith only [h14269, h14391, h14470, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14472 | h14472
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14473 | h14473
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14474 | h14474
                    · linarith only [h14389, h14391, h14469, h14474, h8836, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14476 | h14476
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14477 | h14477
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14478 | h14478
                          · linarith only [h14474, h14478, h8836, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14480 | h14480
                            · linarith only [h0, h14268, h14470, h14476, h14478, h14480, hlam]
                            · rcases h0bigk with h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c | h14482c
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [hlam, p14482_0]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [h0, hlam, p14482_1]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [h7600, hlam, p14482_0]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [h8836, hlam, p14482_1]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [h9666, hlam, p14482_1]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [h0, h14470, h14478, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14482_1]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [hlam, p14482_0]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [h9886, hlam, p14482_0]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [h0, h14470, h14478, hc04, hc45, hlam, hphi, p14482_1]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [h14269, hlam, p14482_0]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                rcases p14482_3 (m.d 0 1) (by simp) with h14493 | h14493
                                · linarith only [h14493, h7600, hlam]
                                · rcases p14482_3 (m.d 0 2) (by simp) with h14495 | h14495
                                  · linarith only [h14495, h9886, hlam]
                                  · linarith only [h0, h14495, hlam]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                rcases p14482_3 (m.d 0 1) (by simp) with h14498 | h14498
                                · linarith only [h14498, h7600, hlam]
                                · rcases p14482_3 (m.d 0 2) (by simp) with h14500 | h14500
                                  · linarith only [h14500, h9886, hlam]
                                  · rcases p14482_3 (m.d 0 3) (by simp) with h14502 | h14502
                                    · rcases p14482_3 (m.d 0 4) (by simp) with h14503 | h14503
                                      · linarith only [h14387, h14503, hlam]
                                      · rcases p14482_3 (m.d 0 5) (by simp) with h14505 | h14505
                                        · linarith only [h14388, h14505, hlam]
                                        · linarith only [h14269, h14505, hlam]
                                    · linarith only [h14502, h9886, hlam]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [hlam, p14482_0]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                rcases p14482_3 (m.d 0 1) (by simp) with h14510 | h14510
                                · linarith only [h14510, h7600, hlam]
                                · rcases p14482_3 (m.d 0 2) (by simp) with h14512 | h14512
                                  · linarith only [h14512, h9886, hlam]
                                  · linarith only [h14268, h14512, hlam]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                rcases p14482_3 (m.d 0 1) (by simp) with h14515 | h14515
                                · linarith only [h14515, h7600, hlam]
                                · rcases p14482_3 (m.d 0 2) (by simp) with h14517 | h14517
                                  · linarith only [h14517, h9886, hlam]
                                  · rcases p14482_3 (m.d 0 3) (by simp) with h14519 | h14519
                                    · rcases p14482_3 (m.d 0 4) (by simp) with h14520 | h14520
                                      · linarith only [h14387, h14520, hlam]
                                      · rcases p14482_3 (m.d 0 5) (by simp) with h14522 | h14522
                                        · linarith only [h14388, h14522, hlam]
                                        · rcases h2bigk with h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c | h14524c
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [hlam, p14524_0]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h0, hlam, p14524_1]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h9886, hlam, p14524_0]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14269, h14476, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p14482_1, p14524_1]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14269, hlam, p14524_0]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14470, h14478, hc02, hc45, hlam, hphi, ht23, ht34, p14524_1]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [hlam, p14524_0]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14391, hlam, p14524_0]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14470, h14476, h14478, hc34, hc45, hlam, hphi, p14524_1]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14470, hlam, p14524_0]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            rcases p14524_3 (m.d 0 2) (by simp) with h14535 | h14535
                                            · linarith only [h14535, hlam, p14524_0]
                                            · rcases p14524_3 (m.d 1 2) (by simp) with h14537 | h14537
                                              · linarith only [h14391, h14537, hlam]
                                              · linarith only [h0, h14537, hlam]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p14524_1]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [hlam, p14524_0]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14268, h14269, h14391, h7600, hlam, p14482_1, p14524_2]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14470, h9666, hc01, hc23, hlam, hphi, ht12, p14524_1]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14268, hlam, p14524_0]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14469, hlam, p14524_0]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14476, hlam, p14524_1]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [hlam, p14524_0]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14478, hlam, p14524_1]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14268, h14478, hc24, hc45, hlam, hphi, p14524_1]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14469, h14478, h8836, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14524_1]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [h14477, hlam, p14524_1]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            rcases p14524_3 (m.d 0 2) (by simp) with h14552 | h14552
                                            · linarith only [h14269, h14552, hlam]
                                            · linarith only [h14268, h14552, hlam]
                                          · have p14524_0 := h14524c.1
                                            have p14524_1 := h14524c.2.1
                                            have p14524_2 := h14524c.2.2.1
                                            have p14524_3 := h14524c.2.2.2
                                            linarith only [hlam, p14524_0]
                                    · linarith only [h14388, h14519, hlam]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [h14268, h9886, hc01, hc23, hlam, hphi, ht12, p14482_1]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [h14268, hlam, p14482_0]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [h14387, hlam, p14482_0]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [hlam, p14482_0]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [h14389, hlam, p14482_0]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                rcases p14482_3 (m.d 0 1) (by simp) with h14562 | h14562
                                · linarith only [h14562, h9666, hlam]
                                · rcases p14482_3 (m.d 0 2) (by simp) with h14564 | h14564
                                  · linarith only [h14269, h14564, hlam]
                                  · linarith only [h0, h14564, hlam]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [h14268, h14269, h14478, hc24, hc45, hlam, hphi, p14482_1]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [h14388, hlam, p14482_0]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                rcases p14482_3 (m.d 0 1) (by simp) with h14569 | h14569
                                · linarith only [h14569, h9666, hlam]
                                · rcases p14482_3 (m.d 0 2) (by simp) with h14571 | h14571
                                  · linarith only [h14269, h14571, hlam]
                                  · linarith only [h14268, h14571, hlam]
                              · have p14482_0 := h14482c.1
                                have p14482_1 := h14482c.2.1
                                have p14482_2 := h14482c.2.2.1
                                have p14482_3 := h14482c.2.2.2
                                linarith only [hlam, p14482_0]
                        · linarith only [h14388, h14391, h14477, h7600, hlam]
                      · linarith only [h14387, h14391, h14476, h7600, hlam]
                  · linarith only [h14388, h14473, h7600, hlam]
                · linarith only [h14387, h14388, h14391, h14469, h14472, h7600, h8836, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h0, h14268, h14469, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14580 | h14580
        · linarith only [h14268, h14388, h14580, h9886, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14582 | h14582
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14583 | h14583
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14584 | h14584
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14585 | h14585
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14586 | h14586
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14587 | h14587
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14588 | h14588
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14589 | h14589
                        · linarith only [h14268, h14388, h14582, h14589, h8836, h9886, hc01, hc12, hlam, hphi]
                        · linarith only [h14268, h14586, h14588, h14589, h9886, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h14387, h14588, h9886, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14593 | h14593
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14594 | h14594
                        · linarith only [h14388, h14582, h14594, h7600, hc01, hc12, hlam, hphi]
                        · linarith only [h14268, h14582, h14586, h14593, h14594, h9886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h14387, h14593, h9886, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14598 | h14598
                    · linarith only [h14580, h14585, h14586, h14598, h8836, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14600 | h14600
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14601 | h14601
                        · linarith only [h14582, h14586, h14601, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14603 | h14603
                          · linarith only [h0, h14268, h14598, h14603, h9666, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14605 | h14605
                            · linarith only [h14269, h14387, h14582, h14584, h14586, h14598, h14605, h9886, hc02, hc35, hlam, hphi, ht23]
                            · linarith only [h14268, h14582, h14586, h14600, h14605, h9886, hc34, hc45, hlam, hphi]
                      · linarith only [h14268, h14387, h14600, h9886, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h14268, h14387, h14582, h14585, h9886, hlam]
              · linarith only [h14268, h14582, h14584, h9886, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h14268, h14582, h14583, h9886, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14612 | h14612
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14613 | h14613
              · linarith only [h14268, h14269, h14582, h14613, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14615 | h14615
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14616 | h14616
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14617 | h14617
                    · linarith only [h14580, h14582, h14612, h14617, h8836, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14619 | h14619
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14620 | h14620
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14621 | h14621
                          · linarith only [h0, h14268, h14613, h14617, h14620, h14621, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14623 | h14623
                            · linarith only [h14268, h14388, h14582, h14613, h14616, h14619, h14621, h14623, h9886, hc12, hc23, hlam, hphi]
                            · rcases h0bigk with h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c | h14625c
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [hlam, p14625_0]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h0, hlam, p14625_1]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h7600, hlam, p14625_0]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h8836, hlam, p14625_1]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h9666, hlam, p14625_1]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14388, h14582, h14616, h9886, hc01, hc23, hlam, hphi, ht12, p14625_1]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [hlam, p14625_0]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h9886, hlam, p14625_0]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14388, h14582, h14616, h8836, h9886, hc01, hc23, hlam, hphi, ht12, p14625_1]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14269, hlam, p14625_0]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14388, h14582, h14616, hc01, hc23, hlam, hphi, ht12, p14625_1]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14268, h14388, h14582, h14616, h14619, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14625_1]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [hlam, p14625_0]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14388, h14582, h14616, h8836, hc01, hc23, hlam, hphi, ht12, p14625_1]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14388, hlam, p14625_1]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14612, h14613, h8836, hc01, hc25, hlam, hphi, ht12, p14625_1]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14268, hlam, p14625_0]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14387, hlam, p14625_0]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [hlam, p14625_0]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14580, hlam, p14625_0]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14388, h14582, h14616, hc01, hc23, hlam, hphi, ht12, p14625_1]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14268, h14269, h14619, h14621, hc34, hc45, hlam, hphi, p14625_1]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14268, h14388, h14582, h14616, h14619, h9886, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14625_1]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [h14388, h14582, h14616, h8836, hc01, hc23, hlam, hphi, ht12, p14625_1]
                              · have p14625_0 := h14625c.1
                                have p14625_1 := h14625c.2.1
                                have p14625_2 := h14625c.2.2.1
                                have p14625_3 := h14625c.2.2.2
                                linarith only [hlam, p14625_0]
                        · linarith only [h14582, h14616, h14620, hlam]
                      · linarith only [h14387, h14582, h14619, h7600, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14653 | h14653
                    · linarith only [h14580, h14582, h14612, h14616, h14653, h8836, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14655 | h14655
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14656 | h14656
                        · linarith only [h0, h14582, h14616, h14656, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h14582, h14612, h14656, h8836, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h14582, h14612, h14655, h8836, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h14387, h14615, h7600, hlam]
            · linarith only [h0, h14268, h14612, hlam]
    · linarith only [h14268, h14387, h9886, hlam]

set_option maxHeartbeats 11598000 in
set_option maxHeartbeats 11598000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h9886 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14268 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h14663 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  rcases m.htr 0 3 4 (by decide) (by decide) with h14664 | h14664
  · rcases m.htr 0 3 5 (by decide) (by decide) with h14665 | h14665
    · rcases m.htr 0 4 5 (by decide) (by decide) with h14666 | h14666
      · rcases m.htr 1 2 3 (by decide) (by decide) with h14667 | h14667
        · linarith only [h14663, h14667, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h14669 | h14669
          · linarith only [h14268, h14663, h14667, h14669, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h14671 | h14671
            · rcases m.htr 1 3 4 (by decide) (by decide) with h14672 | h14672
              · rcases m.htr 1 3 5 (by decide) (by decide) with h14673 | h14673
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14674 | h14674
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14675 | h14675
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14676 | h14676
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14677 | h14677
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h14678 | h14678
                          · rcases h0bigk with h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c | h14679c
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [hlam, p14679_0]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h0, hlam, p14679_1]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h7600, hlam, p14679_0]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h8836, hlam, p14679_1]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h9666, hlam, p14679_1]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h0, h14669, h14675, hc01, hc23, hlam, hphi, ht12, p14679_1]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [hlam, p14679_0]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h9886, hlam, p14679_0]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h14268, hlam, p14679_1]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h0, h14669, h14675, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p14679_1, u5ehi0]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              rcases p14679_3 (m.d 0 1) (by simp) with h14690 | h14690
                              · linarith only [h14690, h7600, hlam]
                              · rcases p14679_3 (m.d 0 2) (by simp) with h14692 | h14692
                                · linarith only [h14692, h9886, hlam]
                                · linarith only [h0, h14692, hlam]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h14663, h14676, h14678, hc03, hlam, hphi, ht0b, ht5b, p14679_1, u5ehi4]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [hlam, p14679_0]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h14268, h14663, h14676, h14678, h9886, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p14679_1, u5ehi4]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              rcases p14679_3 (m.d 0 1) (by simp) with h14698 | h14698
                              · linarith only [h14698, h7600, hlam]
                              · rcases p14679_3 (m.d 0 2) (by simp) with h14700 | h14700
                                · linarith only [h14700, h9886, hlam]
                                · linarith only [h14663, h14700, hlam]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              rcases p14679_3 (m.d 0 1) (by simp) with h14703 | h14703
                              · linarith only [h14703, h8836, hlam]
                              · rcases p14679_3 (m.d 0 2) (by simp) with h14705 | h14705
                                · linarith only [h14268, h14705, hlam]
                                · linarith only [h0, h14705, hlam]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h14663, h14676, h14678, hc04, hlam, hphi, ht0b, ht5b, p14679_1, u5ehi4]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h14664, hlam, p14679_0]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [hlam, p14679_0]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              rcases p14679_3 (m.d 0 1) (by simp) with h14711 | h14711
                              · linarith only [h14711, h8836, hlam]
                              · rcases p14679_3 (m.d 0 2) (by simp) with h14713 | h14713
                                · linarith only [h14268, h14713, hlam]
                                · linarith only [h14663, h14713, hlam]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h0, h14663, h14669, h14675, hc01, hc23, hlam, hphi, ht12, p14679_1]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h14663, hlam, p14679_1]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h14665, hlam, p14679_0]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [h14666, hlam, p14679_1]
                            · have p14679_0 := h14679c.1
                              have p14679_1 := h14679c.2.1
                              have p14679_2 := h14679c.2.2.1
                              have p14679_3 := h14679c.2.2.2
                              linarith only [hlam, p14679_0]
                          · rcases h0bigk with h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c | h14721c
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [hlam, p14721_0]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h0, hlam, p14721_1]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h7600, hlam, p14721_0]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h8836, hlam, p14721_1]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h9666, hlam, p14721_1]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h0, h14669, h14675, hc01, hc23, hlam, hphi, ht12, p14721_1]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [hlam, p14721_0]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h9886, hlam, p14721_0]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h14268, hlam, p14721_1]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h0, h14669, h14675, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p14721_1, u5ehi0]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              rcases p14721_3 (m.d 0 1) (by simp) with h14732 | h14732
                              · linarith only [h14732, h7600, hlam]
                              · rcases p14721_3 (m.d 0 2) (by simp) with h14734 | h14734
                                · linarith only [h14734, h9886, hlam]
                                · linarith only [h0, h14734, hlam]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h14663, h14667, h7600, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p14721_1, u5ehi2]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [hlam, p14721_0]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h14268, h14663, h14667, h14677, h14678, h7600, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14721_1]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              rcases p14721_3 (m.d 0 1) (by simp) with h14740 | h14740
                              · linarith only [h14740, h7600, hlam]
                              · rcases p14721_3 (m.d 0 2) (by simp) with h14742 | h14742
                                · linarith only [h14742, h9886, hlam]
                                · linarith only [h14663, h14742, hlam]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              rcases p14721_3 (m.d 0 1) (by simp) with h14745 | h14745
                              · linarith only [h14745, h8836, hlam]
                              · rcases p14721_3 (m.d 0 2) (by simp) with h14747 | h14747
                                · linarith only [h14268, h14747, hlam]
                                · linarith only [h0, h14747, hlam]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h14663, h14677, h14678, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p14721_1]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h14664, hlam, p14721_0]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [hlam, p14721_0]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              rcases p14721_3 (m.d 0 1) (by simp) with h14753 | h14753
                              · linarith only [h14753, h8836, hlam]
                              · rcases p14721_3 (m.d 0 2) (by simp) with h14755 | h14755
                                · linarith only [h14268, h14755, hlam]
                                · linarith only [h14663, h14755, hlam]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h0, h14663, h14669, h14675, hc01, hc23, hlam, hphi, ht12, p14721_1]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h14663, hlam, p14721_1]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h14665, hlam, p14721_0]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [h14666, hlam, p14721_1]
                            · have p14721_0 := h14721c.1
                              have p14721_1 := h14721c.2.1
                              have p14721_2 := h14721c.2.2.1
                              have p14721_3 := h14721c.2.2.2
                              linarith only [hlam, p14721_0]
                        · linarith only [h0, h14669, h14677, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h14663, h14676, h9886, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h14663, h14667, h14675, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h14664, h14666, h14674, h7600, h8836, hc01, hc13, hlam, hphi]
                · linarith only [h14663, h14665, h14673, h7600, h9886, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h14664, h14672, h7600, hlam]
            · linarith only [h0, h14663, h14671, hlam]
      · linarith only [h14268, h14663, h14666, hlam]
    · linarith only [h14268, h14663, h14664, h14665, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h14772 | h14772
    · rcases m.htr 0 4 5 (by decide) (by decide) with h14773 | h14773
      · rcases m.htr 1 2 3 (by decide) (by decide) with h14774 | h14774
        · linarith only [h14663, h14774, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h14776 | h14776
          · linarith only [h14268, h14663, h14776, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h14778 | h14778
            · rcases m.htr 1 3 4 (by decide) (by decide) with h14779 | h14779
              · linarith only [h14664, h14772, h14779, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h14781 | h14781
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14782 | h14782
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14783 | h14783
                    · linarith only [h0, h14774, h14779, h14783, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h14663, h14783, h9886, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h14773, h14782, h8836, hlam]
                · linarith only [h0, h14663, h14772, h14774, h14781, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
            · linarith only [h0, h14663, h14778, hlam]
      · linarith only [h14663, h14664, h14773, h9886, hlam]
    · linarith only [h14663, h14772, h9886, hlam]

end R2N4
