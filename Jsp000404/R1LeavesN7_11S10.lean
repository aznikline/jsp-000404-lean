import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12210000 in
set_option maxHeartbeats 12210000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5004 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h5239 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 5 (by decide) (by decide) with h5240 | h5240
  · rcases m.htr 1 3 4 (by decide) (by decide) with h5241 | h5241
    · linarith only [h5241, h6, hc13, hlam, hphi, ht01, u0ehi2]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h5243 | h5243
      · linarith only [h1, h5004, h5243, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5245 | h5245
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5246 | h5246
          · linarith only [h5239, h5246, h6, hc12, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5248 | h5248
            · linarith only [h1, h5004, h5239, h5248, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5250 | h5250
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5251 | h5251
                · rcases h2bigk with h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c | h5252c
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    rcases p5252_3 (m.d 0 2) (by simp) with h5254 | h5254
                    · rcases p5252_3 (m.d 1 2) (by simp) with h5255 | h5255
                      · linarith only [h0, h5255, hlam]
                      · rcases p5252_3 (m.d 2 3) (by simp) with h5257 | h5257
                        · linarith only [h3, h5257, hlam]
                        · rcases p5252_3 (m.d 2 4) (by simp) with h5259 | h5259
                          · linarith only [h4, h5259, hlam]
                          · rcases p5252_3 (m.d 2 5) (by simp) with h5261 | h5261
                            · linarith only [h5, h5261, hlam]
                            · rcases h3bigk with h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c | h5263c
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [hlam, p5263_0]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [h5004, h5251, hc13, hc34, hlam, hphi, p5263_1]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [h5004, h5251, hc23, hc34, hlam, hphi, p5263_1]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [h6, hlam, p5263_0]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [h5004, hlam, p5263_0]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [h1, hlam, p5263_0]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [hlam, p5263_0]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [h1, h5004, h5251, hc23, hc34, hlam, hphi, p5263_1]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [h5241, hlam, p5263_0]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [h5243, hlam, p5263_0]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [h3, hlam, p5263_0]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [h5239, hlam, p5263_0]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [hlam, p5263_0]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [h5246, hlam, p5263_0]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [h5248, hlam, p5263_0]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p5263_1, u0ehi2]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                rcases p5263_3 (m.d 0 3) (by simp) with h5280 | h5280
                                · linarith only [h5280, h6, hlam]
                                · linarith only [h1, h5280, hlam]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                rcases p5263_3 (m.d 0 3) (by simp) with h5283 | h5283
                                · linarith only [h5283, h6, hlam]
                                · linarith only [h3, h5283, hlam]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [hlam, p5263_0]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [h5004, hc34, hlam, hphi, ht01, ht12, ht23, p5263_1, u0ehi2]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p5263_1, u0ehi2]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                rcases p5263_3 (m.d 0 3) (by simp) with h5289 | h5289
                                · linarith only [h5004, h5289, hlam]
                                · linarith only [h1, h5289, hlam]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                rcases p5263_3 (m.d 0 3) (by simp) with h5292 | h5292
                                · linarith only [h5004, h5292, hlam]
                                · linarith only [h3, h5292, hlam]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [h5251, hlam, p5263_0]
                              · have p5263_0 := h5263c.1
                                have p5263_1 := h5263c.2.1
                                have p5263_2 := h5263c.2.2.1
                                have p5263_3 := h5263c.2.2.2
                                linarith only [hlam, p5263_0]
                    · linarith only [h0, h5254, hlam]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    rcases p5252_3 (m.d 0 2) (by simp) with h5298 | h5298
                    · rcases p5252_3 (m.d 1 2) (by simp) with h5299 | h5299
                      · linarith only [h0, h5299, hlam]
                      · linarith only [h5239, h5299, hlam]
                    · linarith only [h5298, hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    rcases p5252_3 (m.d 0 2) (by simp) with h5303 | h5303
                    · rcases p5252_3 (m.d 1 2) (by simp) with h5304 | h5304
                      · linarith only [h0, h5304, hlam]
                      · rcases p5252_3 (m.d 2 3) (by simp) with h5306 | h5306
                        · linarith only [h3, h5306, hlam]
                        · rcases p5252_3 (m.d 2 4) (by simp) with h5308 | h5308
                          · linarith only [h5308, hlam, p5252_0]
                          · rcases p5252_3 (m.d 2 5) (by simp) with h5310 | h5310
                            · linarith only [h5, h5310, hlam]
                            · rcases h3bigk with h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c | h5312c
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [hlam, p5312_0]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [h6, hc13, hc34, hlam, hphi, p5312_1]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [h6, hc23, hc34, hlam, hphi, p5312_1]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [h6, hlam, p5312_0]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [h5004, hlam, p5312_0]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [h1, hlam, p5312_0]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [hlam, p5312_0]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [h1, h5004, h5251, hc23, hc34, hlam, hphi, p5312_1]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [h5241, hlam, p5312_0]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [h5243, hlam, p5312_0]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [h3, hlam, p5312_0]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [h5239, hlam, p5312_0]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [hlam, p5312_0]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [h5246, hlam, p5312_0]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [h5248, hlam, p5312_0]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p5312_1, u0ehi2]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                rcases p5312_3 (m.d 0 3) (by simp) with h5329 | h5329
                                · linarith only [h5329, h6, hlam]
                                · linarith only [h1, h5329, hlam]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                rcases p5312_3 (m.d 0 3) (by simp) with h5332 | h5332
                                · linarith only [h5332, h6, hlam]
                                · linarith only [h3, h5332, hlam]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [hlam, p5312_0]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [h5004, hc34, hlam, hphi, ht01, ht12, ht23, p5312_1, u0ehi2]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p5312_1, u0ehi2]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                rcases p5312_3 (m.d 0 3) (by simp) with h5338 | h5338
                                · linarith only [h5004, h5338, hlam]
                                · linarith only [h1, h5338, hlam]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                rcases p5312_3 (m.d 0 3) (by simp) with h5341 | h5341
                                · linarith only [h5004, h5341, hlam]
                                · linarith only [h3, h5341, hlam]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [h5251, hlam, p5312_0]
                              · have p5312_0 := h5312c.1
                                have p5312_1 := h5312c.2.1
                                have p5312_2 := h5312c.2.2.1
                                have p5312_3 := h5312c.2.2.2
                                linarith only [hlam, p5312_0]
                    · linarith only [h5303, hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    rcases p5252_3 (m.d 0 2) (by simp) with h5347 | h5347
                    · rcases p5252_3 (m.d 1 2) (by simp) with h5348 | h5348
                      · linarith only [h0, h5348, hlam]
                      · linarith only [h5240, h5348, hlam]
                    · linarith only [h5347, hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [h0, hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    rcases p5252_3 (m.d 0 2) (by simp) with h5354 | h5354
                    · rcases p5252_3 (m.d 1 2) (by simp) with h5355 | h5355
                      · rcases p5252_3 (m.d 2 3) (by simp) with h5356 | h5356
                        · linarith only [h5356, hlam, p5252_0]
                        · rcases p5252_3 (m.d 2 4) (by simp) with h5358 | h5358
                          · rcases p5252_3 (m.d 2 5) (by simp) with h5359 | h5359
                            · linarith only [h5240, h5359, hlam]
                            · linarith only [h5248, h5359, hlam]
                          · linarith only [h5246, h5358, hlam]
                      · linarith only [h5355, hlam, p5252_0]
                    · linarith only [h3, h5354, hlam]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [h0, h5250, hc01, hc45, hlam, hphi, ht0b, ht5b, p5252_1]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    rcases p5252_3 (m.d 0 2) (by simp) with h5366 | h5366
                    · rcases p5252_3 (m.d 1 2) (by simp) with h5367 | h5367
                      · rcases p5252_3 (m.d 2 3) (by simp) with h5368 | h5368
                        · linarith only [h5239, h5368, hlam]
                        · rcases p5252_3 (m.d 2 4) (by simp) with h5370 | h5370
                          · rcases p5252_3 (m.d 2 5) (by simp) with h5371 | h5371
                            · linarith only [h5371, hlam, p5252_0]
                            · rcases h3bigk with h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [hlam, p5373_0]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [h6, hc13, hc34, hlam, hphi, p5373_1]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [h6, hc23, hc34, hlam, hphi, p5373_1]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [h6, hlam, p5373_0]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [h5004, hlam, p5373_0]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [h1, hlam, p5373_0]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [hlam, p5373_0]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [h1, h5004, h5251, hc23, hc34, hlam, hphi, p5373_1]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [h5241, hlam, p5373_0]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [h5243, hlam, p5373_0]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [h3, hlam, p5373_0]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [h5239, hlam, p5373_0]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [hlam, p5373_0]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [h5246, hlam, p5373_0]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [h5248, hlam, p5373_0]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p5373_1, u0ehi2]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                rcases p5373_3 (m.d 0 3) (by simp) with h5390 | h5390
                                · linarith only [h5390, h6, hlam]
                                · linarith only [h1, h5390, hlam]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                rcases p5373_3 (m.d 0 3) (by simp) with h5393 | h5393
                                · linarith only [h5393, h6, hlam]
                                · linarith only [h3, h5393, hlam]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [hlam, p5373_0]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [h5004, hc34, hlam, hphi, ht01, ht12, ht23, p5373_1, u0ehi2]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p5373_1, u0ehi2]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                rcases p5373_3 (m.d 0 3) (by simp) with h5399 | h5399
                                · linarith only [h5004, h5399, hlam]
                                · linarith only [h1, h5399, hlam]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                rcases p5373_3 (m.d 0 3) (by simp) with h5402 | h5402
                                · linarith only [h5004, h5402, hlam]
                                · linarith only [h3, h5402, hlam]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [h5251, hlam, p5373_0]
                              · have p5373_0 := h5373c.1
                                have p5373_1 := h5373c.2.1
                                have p5373_2 := h5373c.2.2.1
                                have p5373_3 := h5373c.2.2.2
                                linarith only [hlam, p5373_0]
                          · linarith only [h5250, h5370, hlam]
                      · linarith only [h5367, hlam, p5252_0]
                    · linarith only [h5, h5366, hlam]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [h3, hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [h5239, hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [h5246, hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [h5248, hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [h4, hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [h4, h5239, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5252_1]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    rcases p5252_3 (m.d 0 2) (by simp) with h5417 | h5417
                    · rcases p5252_3 (m.d 1 2) (by simp) with h5418 | h5418
                      · rcases p5252_3 (m.d 2 3) (by simp) with h5419 | h5419
                        · linarith only [h5246, h5419, hlam]
                        · rcases p5252_3 (m.d 2 4) (by simp) with h5421 | h5421
                          · rcases p5252_3 (m.d 2 5) (by simp) with h5422 | h5422
                            · linarith only [h5250, h5422, hlam]
                            · linarith only [h5248, h5422, hlam]
                          · linarith only [h5246, h5421, hlam]
                      · linarith only [h5239, h5418, hlam]
                    · linarith only [h3, h5417, hlam]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    rcases p5252_3 (m.d 0 2) (by simp) with h5429 | h5429
                    · rcases p5252_3 (m.d 1 2) (by simp) with h5430 | h5430
                      · rcases p5252_3 (m.d 2 3) (by simp) with h5431 | h5431
                        · linarith only [h5246, h5431, hlam]
                        · rcases p5252_3 (m.d 2 4) (by simp) with h5433 | h5433
                          · rcases p5252_3 (m.d 2 5) (by simp) with h5434 | h5434
                            · linarith only [h5250, h5434, hlam]
                            · rcases h3bigk with h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [hlam, p5436_0]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [h6, hc13, hc34, hlam, hphi, p5436_1]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [h6, hc23, hc34, hlam, hphi, p5436_1]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [h6, hlam, p5436_0]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [h5004, hlam, p5436_0]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [h1, hlam, p5436_0]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [hlam, p5436_0]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [h1, h5004, h5251, hc23, hc34, hlam, hphi, p5436_1]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [h5241, hlam, p5436_0]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [h5243, hlam, p5436_0]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [h3, hlam, p5436_0]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [h5239, hlam, p5436_0]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [hlam, p5436_0]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [h5246, hlam, p5436_0]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [h5248, hlam, p5436_0]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p5436_1, u0ehi2]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                rcases p5436_3 (m.d 0 3) (by simp) with h5453 | h5453
                                · linarith only [h5453, h6, hlam]
                                · linarith only [h1, h5453, hlam]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                rcases p5436_3 (m.d 0 3) (by simp) with h5456 | h5456
                                · linarith only [h5456, h6, hlam]
                                · linarith only [h3, h5456, hlam]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [hlam, p5436_0]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [h5004, hc34, hlam, hphi, ht01, ht12, ht23, p5436_1, u0ehi2]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p5436_1, u0ehi2]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                rcases p5436_3 (m.d 0 3) (by simp) with h5462 | h5462
                                · linarith only [h5004, h5462, hlam]
                                · linarith only [h1, h5462, hlam]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                rcases p5436_3 (m.d 0 3) (by simp) with h5465 | h5465
                                · linarith only [h5004, h5465, hlam]
                                · linarith only [h3, h5465, hlam]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [h5251, hlam, p5436_0]
                              · have p5436_0 := h5436c.1
                                have p5436_1 := h5436c.2.1
                                have p5436_2 := h5436c.2.2.1
                                have p5436_3 := h5436c.2.2.2
                                linarith only [hlam, p5436_0]
                          · linarith only [h5250, h5433, hlam]
                      · linarith only [h5240, h5430, hlam]
                    · linarith only [h5, h5429, hlam]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [h5, hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [h5240, hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [h0, h5240, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5252_1]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [h5250, hlam, p5252_0]
                  · have p5252_0 := h5252c.1
                    have p5252_1 := h5252c.2.1
                    have p5252_2 := h5252c.2.2.1
                    have p5252_3 := h5252c.2.2.2
                    linarith only [hlam, p5252_0]
                · linarith only [h5251, h6, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5479 | h5479
                · rcases h2bigk with h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    rcases p5480_3 (m.d 0 2) (by simp) with h5482 | h5482
                    · rcases p5480_3 (m.d 1 2) (by simp) with h5483 | h5483
                      · linarith only [h0, h5483, hlam]
                      · rcases p5480_3 (m.d 2 3) (by simp) with h5485 | h5485
                        · linarith only [h3, h5485, hlam]
                        · rcases p5480_3 (m.d 2 4) (by simp) with h5487 | h5487
                          · linarith only [h4, h5487, hlam]
                          · rcases p5480_3 (m.d 2 5) (by simp) with h5489 | h5489
                            · linarith only [h5, h5489, hlam]
                            · rcases h3bigk with h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c | h5491c
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [hlam, p5491_0]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h5004, hc13, hc35, hlam, hphi, p5491_1]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h5004, hc23, hc35, hlam, hphi, p5491_1]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h6, hlam, p5491_0]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h5004, hlam, p5491_0]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h1, hlam, p5491_0]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [hlam, p5491_0]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h1, h5004, hc23, hc35, hlam, hphi, p5491_1]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h5241, hlam, p5491_0]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h5243, hlam, p5491_0]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h3, hlam, p5491_0]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h5239, hlam, p5491_0]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [hlam, p5491_0]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h5246, hlam, p5491_0]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h5248, hlam, p5491_0]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p5491_1, u0ehi2]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                rcases p5491_3 (m.d 0 3) (by simp) with h5508 | h5508
                                · linarith only [h5508, h6, hlam]
                                · linarith only [h1, h5508, hlam]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                rcases p5491_3 (m.d 0 3) (by simp) with h5511 | h5511
                                · linarith only [h5511, h6, hlam]
                                · linarith only [h3, h5511, hlam]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [hlam, p5491_0]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h0, h5004, h5240, h5245, h5246, h5250, hc01, hc23, hc34, hlam, hphi, p5480_1, p5491_1, u0ehi2]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h0, h5240, h5245, h5246, h5250, hc01, hc23, hc35, hlam, hphi, p5480_1, p5491_1, u0ehi2]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                rcases p5491_3 (m.d 0 3) (by simp) with h5517 | h5517
                                · linarith only [h5004, h5517, hlam]
                                · linarith only [h1, h5517, hlam]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                rcases p5491_3 (m.d 0 3) (by simp) with h5520 | h5520
                                · linarith only [h5004, h5520, hlam]
                                · linarith only [h3, h5520, hlam]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [h5479, hlam, p5491_0]
                              · have p5491_0 := h5491c.1
                                have p5491_1 := h5491c.2.1
                                have p5491_2 := h5491c.2.2.1
                                have p5491_3 := h5491c.2.2.2
                                linarith only [hlam, p5491_0]
                    · linarith only [h0, h5482, hlam]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    rcases p5480_3 (m.d 0 2) (by simp) with h5526 | h5526
                    · rcases p5480_3 (m.d 1 2) (by simp) with h5527 | h5527
                      · linarith only [h0, h5527, hlam]
                      · linarith only [h5239, h5527, hlam]
                    · linarith only [h5526, hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    rcases p5480_3 (m.d 0 2) (by simp) with h5531 | h5531
                    · rcases p5480_3 (m.d 1 2) (by simp) with h5532 | h5532
                      · linarith only [h0, h5532, hlam]
                      · linarith only [h5240, h5245, h5250, h5532, hlam]
                    · linarith only [h5531, hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    rcases p5480_3 (m.d 0 2) (by simp) with h5536 | h5536
                    · rcases p5480_3 (m.d 1 2) (by simp) with h5537 | h5537
                      · linarith only [h0, h5537, hlam]
                      · linarith only [h5240, h5537, hlam]
                    · linarith only [h5536, hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [h0, hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    rcases p5480_3 (m.d 0 2) (by simp) with h5543 | h5543
                    · rcases p5480_3 (m.d 1 2) (by simp) with h5544 | h5544
                      · rcases p5480_3 (m.d 2 3) (by simp) with h5545 | h5545
                        · linarith only [h5545, hlam, p5480_0]
                        · rcases p5480_3 (m.d 2 4) (by simp) with h5547 | h5547
                          · linarith only [h5250, h5547, hc23, hc45, hlam, hphi, ht34, p5480_1]
                          · linarith only [h5246, h5547, hlam]
                      · linarith only [h5544, hlam, p5480_0]
                    · linarith only [h3, h5543, hlam]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    rcases p5480_3 (m.d 0 2) (by simp) with h5552 | h5552
                    · rcases p5480_3 (m.d 1 2) (by simp) with h5553 | h5553
                      · rcases p5480_3 (m.d 2 3) (by simp) with h5554 | h5554
                        · linarith only [h5239, h5554, hlam]
                        · rcases p5480_3 (m.d 2 4) (by simp) with h5556 | h5556
                          · linarith only [h5556, hlam, p5480_0]
                          · rcases p5480_3 (m.d 2 5) (by simp) with h5558 | h5558
                            · linarith only [h5240, h5558, hlam]
                            · linarith only [h5250, h5558, hlam]
                      · linarith only [h5553, hlam, p5480_0]
                    · linarith only [h4, h5552, hlam]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    rcases p5480_3 (m.d 0 2) (by simp) with h5563 | h5563
                    · rcases p5480_3 (m.d 1 2) (by simp) with h5564 | h5564
                      · rcases p5480_3 (m.d 2 3) (by simp) with h5565 | h5565
                        · linarith only [h5239, h5565, hlam]
                        · rcases p5480_3 (m.d 2 4) (by simp) with h5567 | h5567
                          · linarith only [h5250, h5567, hlam, p5480_1]
                          · rcases p5480_3 (m.d 2 5) (by simp) with h5569 | h5569
                            · linarith only [h5569, hlam, p5480_0]
                            · rcases h3bigk with h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c | h5571c
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [hlam, p5571_0]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [h6, hc13, hc34, hlam, hphi, p5571_1]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [h6, hc23, hc34, hlam, hphi, p5571_1]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [h6, hlam, p5571_0]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [h5004, hlam, p5571_0]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [h1, hlam, p5571_0]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [hlam, p5571_0]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [h1, h5004, h5479, hc23, hc34, hlam, hphi, p5571_1]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [h5241, hlam, p5571_0]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [h5243, hlam, p5571_0]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [h3, hlam, p5571_0]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [h5239, hlam, p5571_0]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [hlam, p5571_0]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [h5246, hlam, p5571_0]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [h5248, hlam, p5571_0]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p5571_1, u0ehi2]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                rcases p5571_3 (m.d 0 3) (by simp) with h5588 | h5588
                                · linarith only [h5588, h6, hlam]
                                · linarith only [h1, h5588, hlam]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                rcases p5571_3 (m.d 0 3) (by simp) with h5591 | h5591
                                · linarith only [h5591, h6, hlam]
                                · linarith only [h3, h5591, hlam]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [hlam, p5571_0]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [h5004, hc34, hlam, hphi, ht01, ht12, ht23, p5571_1, u0ehi4]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p5571_1, u0ehi2]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                rcases p5571_3 (m.d 0 3) (by simp) with h5597 | h5597
                                · linarith only [h5004, h5597, hlam]
                                · linarith only [h1, h5597, hlam]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                rcases p5571_3 (m.d 0 3) (by simp) with h5600 | h5600
                                · linarith only [h5004, h5600, hlam]
                                · linarith only [h3, h5600, hlam]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [h5479, hlam, p5571_0]
                              · have p5571_0 := h5571c.1
                                have p5571_1 := h5571c.2.1
                                have p5571_2 := h5571c.2.2.1
                                have p5571_3 := h5571c.2.2.2
                                linarith only [hlam, p5571_0]
                      · linarith only [h5564, hlam, p5480_0]
                    · linarith only [h5, h5563, hlam]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [h3, hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [h5239, hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [h5246, hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [h5248, hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [h4, hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [h0, h5, h5239, h5250, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5480_1]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [h0, h5240, h5250, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5480_1]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [h5250, hlam, p5480_1]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [h5, hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [h5240, hlam, p5480_0]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [h0, h5240, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5480_1]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [h0, h5240, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p5480_1]
                  · have p5480_0 := h5480c.1
                    have p5480_1 := h5480c.2.1
                    have p5480_2 := h5480c.2.2.1
                    have p5480_3 := h5480c.2.2.2
                    linarith only [hlam, p5480_0]
                · linarith only [h2, h5245, h5479, h6, hc01, hlam, hphi, u0ehi3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5623 | h5623
          · linarith only [h5238, h5239, h5241, h5245, h5623, h6, hc04, hlam, hphi, u0ehi2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5625 | h5625
            · linarith only [h5004, h5238, h5239, h5241, h5245, h5625, h6, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5627 | h5627
              · linarith only [h5240, h5245, h5627, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5629 | h5629
                · rcases h2bigk with h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    rcases p5630_3 (m.d 0 2) (by simp) with h5632 | h5632
                    · rcases p5630_3 (m.d 1 2) (by simp) with h5633 | h5633
                      · linarith only [h0, h5633, hlam]
                      · rcases p5630_3 (m.d 2 3) (by simp) with h5635 | h5635
                        · linarith only [h3, h5635, hlam]
                        · rcases p5630_3 (m.d 2 4) (by simp) with h5637 | h5637
                          · linarith only [h4, h5637, hlam]
                          · rcases p5630_3 (m.d 2 5) (by simp) with h5639 | h5639
                            · linarith only [h5, h5639, hlam]
                            · rcases h3bigk with h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h5004, h5239, hc23, hc35, hlam, hphi, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h5004, hc23, hc35, hlam, hphi, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h6, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h5004, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h1, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h1, h5004, hc23, hc35, hlam, hphi, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h5241, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h5243, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h3, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h5239, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h5623, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h5625, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h0, h5240, h5623, h5627, hc01, hc23, hc34, hlam, hphi, p5630_1, p5641_1, u0ehi2]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                rcases p5641_3 (m.d 0 3) (by simp) with h5658 | h5658
                                · linarith only [h5658, h6, hlam]
                                · linarith only [h1, h5658, hlam]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                rcases p5641_3 (m.d 0 3) (by simp) with h5661 | h5661
                                · linarith only [h5661, h6, hlam]
                                · linarith only [h3, h5661, hlam]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h0, h5004, h5240, h5623, h5627, hc01, hc23, hc34, hlam, hphi, p5630_1, p5641_1, u0ehi2]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h0, h5240, h5623, h5627, hc01, hc23, hc35, hlam, hphi, p5630_1, p5641_1, u0ehi2]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                rcases p5641_3 (m.d 0 3) (by simp) with h5667 | h5667
                                · linarith only [h5004, h5667, hlam]
                                · linarith only [h1, h5667, hlam]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                rcases p5641_3 (m.d 0 3) (by simp) with h5670 | h5670
                                · linarith only [h5004, h5670, hlam]
                                · linarith only [h3, h5670, hlam]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h5629, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [hlam, p5641_0]
                    · linarith only [h0, h5632, hlam]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    rcases p5630_3 (m.d 0 2) (by simp) with h5676 | h5676
                    · rcases p5630_3 (m.d 1 2) (by simp) with h5677 | h5677
                      · linarith only [h0, h5677, hlam]
                      · linarith only [h5239, h5677, hlam]
                    · linarith only [h5676, hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    rcases p5630_3 (m.d 0 2) (by simp) with h5681 | h5681
                    · rcases p5630_3 (m.d 1 2) (by simp) with h5682 | h5682
                      · linarith only [h0, h5682, hlam]
                      · linarith only [h5240, h5627, h5682, hlam]
                    · linarith only [h5681, hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    rcases p5630_3 (m.d 0 2) (by simp) with h5686 | h5686
                    · rcases p5630_3 (m.d 1 2) (by simp) with h5687 | h5687
                      · linarith only [h0, h5687, hlam]
                      · linarith only [h5240, h5687, hlam]
                    · linarith only [h5686, hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [h0, hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    rcases p5630_3 (m.d 0 2) (by simp) with h5693 | h5693
                    · rcases p5630_3 (m.d 1 2) (by simp) with h5694 | h5694
                      · rcases p5630_3 (m.d 2 3) (by simp) with h5695 | h5695
                        · linarith only [h5695, hlam, p5630_0]
                        · rcases p5630_3 (m.d 2 4) (by simp) with h5697 | h5697
                          · linarith only [h5240, h5627, h5697, hlam]
                          · linarith only [h5623, h5697, hlam]
                      · linarith only [h5694, hlam, p5630_0]
                    · linarith only [h3, h5693, hlam]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    rcases p5630_3 (m.d 0 2) (by simp) with h5702 | h5702
                    · rcases p5630_3 (m.d 1 2) (by simp) with h5703 | h5703
                      · rcases p5630_3 (m.d 2 3) (by simp) with h5704 | h5704
                        · linarith only [h5239, h5704, hlam]
                        · rcases p5630_3 (m.d 2 4) (by simp) with h5706 | h5706
                          · linarith only [h5706, hlam, p5630_0]
                          · rcases p5630_3 (m.d 2 5) (by simp) with h5708 | h5708
                            · linarith only [h5240, h5708, hlam]
                            · linarith only [h5627, h5708, hlam]
                      · linarith only [h5703, hlam, p5630_0]
                    · linarith only [h4, h5702, hlam]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    rcases p5630_3 (m.d 0 2) (by simp) with h5713 | h5713
                    · rcases p5630_3 (m.d 1 2) (by simp) with h5714 | h5714
                      · rcases p5630_3 (m.d 2 3) (by simp) with h5715 | h5715
                        · linarith only [h5239, h5715, hlam]
                        · rcases p5630_3 (m.d 2 4) (by simp) with h5717 | h5717
                          · linarith only [h5627, h5717, hlam, p5630_1]
                          · rcases p5630_3 (m.d 2 5) (by simp) with h5719 | h5719
                            · linarith only [h5719, hlam, p5630_0]
                            · rcases h3bigk with h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [hlam, p5721_0]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [h6, hc13, hc34, hlam, hphi, p5721_1]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [h6, hc23, hc34, hlam, hphi, p5721_1]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [h6, hlam, p5721_0]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [h5004, hlam, p5721_0]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [h1, hlam, p5721_0]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [hlam, p5721_0]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [h1, h5004, h5629, hc23, hc34, hlam, hphi, p5721_1]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [h5241, hlam, p5721_0]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [h5243, hlam, p5721_0]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [h3, hlam, p5721_0]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [h5239, hlam, p5721_0]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [hlam, p5721_0]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [h5623, hlam, p5721_0]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [h5625, hlam, p5721_0]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p5721_1, u0ehi2]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                rcases p5721_3 (m.d 0 3) (by simp) with h5738 | h5738
                                · linarith only [h5738, h6, hlam]
                                · linarith only [h1, h5738, hlam]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                rcases p5721_3 (m.d 0 3) (by simp) with h5741 | h5741
                                · linarith only [h5741, h6, hlam]
                                · linarith only [h3, h5741, hlam]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [hlam, p5721_0]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [h5004, hc34, hlam, hphi, ht01, ht12, ht23, p5721_1, u0ehi2]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p5721_1, u0ehi2]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                rcases p5721_3 (m.d 0 3) (by simp) with h5747 | h5747
                                · linarith only [h5004, h5747, hlam]
                                · linarith only [h1, h5747, hlam]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                rcases p5721_3 (m.d 0 3) (by simp) with h5750 | h5750
                                · linarith only [h5004, h5750, hlam]
                                · linarith only [h3, h5750, hlam]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [h5629, hlam, p5721_0]
                              · have p5721_0 := h5721c.1
                                have p5721_1 := h5721c.2.1
                                have p5721_2 := h5721c.2.2.1
                                have p5721_3 := h5721c.2.2.2
                                linarith only [hlam, p5721_0]
                      · linarith only [h5714, hlam, p5630_0]
                    · linarith only [h5, h5713, hlam]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [h3, hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [h5239, hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [h5623, hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [h5625, hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [h4, hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [h0, h4, h5239, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5630_1]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [h5238, h5627, h6, hc23, hc34, hlam, hphi, p5630_1]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [h5627, hlam, p5630_1]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [h5, hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [h5240, hlam, p5630_0]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [h0, h5240, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5630_1]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [h0, h5240, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p5630_1]
                  · have p5630_0 := h5630c.1
                    have p5630_1 := h5630c.2.1
                    have p5630_2 := h5630c.2.2.1
                    have p5630_3 := h5630c.2.2.2
                    linarith only [hlam, p5630_0]
                · linarith only [h5238, h5629, h6, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h5773 | h5773
    · linarith only [h1, h5773, h6, hc01, hlam, hphi, u0ehi3]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h5775 | h5775
      · linarith only [h5, h5004, h5238, h5239, h5240, h5775, hc04, hlam, hphi, u0ehi2]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5777 | h5777
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5778 | h5778
          · linarith only [h0, h5, h5239, h5240, h5778, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5780 | h5780
            · linarith only [h5, h5004, h5239, h5240, h5780, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5782 | h5782
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5783 | h5783
                · rcases h2bigk with h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [hlam, p5784_0]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    rcases p5784_3 (m.d 0 2) (by simp) with h5786 | h5786
                    · rcases p5784_3 (m.d 1 2) (by simp) with h5787 | h5787
                      · linarith only [h0, h5787, hlam]
                      · rcases p5784_3 (m.d 2 3) (by simp) with h5789 | h5789
                        · linarith only [h3, h5789, hlam]
                        · rcases p5784_3 (m.d 2 4) (by simp) with h5791 | h5791
                          · linarith only [h4, h5791, hlam]
                          · linarith only [h5240, h5782, h5791, hlam]
                    · linarith only [h0, h5786, hlam]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h4, h5239, h5240, h5782, hlam, p5784_2]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h0, h5239, h5240, h5782, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5784_1]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h0, h5239, h5240, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5784_1]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h0, hlam, p5784_0]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [hlam, p5784_0]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h0, h4, h5240, h5782, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5784_1]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h5240, h5782, hlam, p5784_1]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h5240, hlam, p5784_0]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h3, hlam, p5784_0]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h5239, hlam, p5784_0]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [hlam, p5784_0]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h5778, hlam, p5784_0]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h5780, hlam, p5784_0]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h4, hlam, p5784_0]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h0, h4, h5239, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5784_1]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    rcases p5784_3 (m.d 0 2) (by simp) with h5810 | h5810
                    · rcases p5784_3 (m.d 1 2) (by simp) with h5811 | h5811
                      · linarith only [h5240, h5782, h5811, hlam]
                      · linarith only [h5239, h5811, hlam]
                    · linarith only [h3, h5810, hlam]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [hlam, p5784_0]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h0, h4, h5240, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5784_1]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h5, hlam, p5784_0]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h0, h5, h5239, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5784_1]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    rcases p5784_3 (m.d 0 2) (by simp) with h5819 | h5819
                    · rcases p5784_3 (m.d 1 2) (by simp) with h5820 | h5820
                      · linarith only [h5240, h5820, hlam]
                      · linarith only [h5239, h5820, hlam]
                    · linarith only [h3, h5819, hlam]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [h5782, hlam, p5784_0]
                  · have p5784_0 := h5784c.1
                    have p5784_1 := h5784c.2.1
                    have p5784_2 := h5784c.2.2.1
                    have p5784_3 := h5784c.2.2.2
                    linarith only [hlam, p5784_0]
                · linarith only [h5783, h6, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
              · linarith only [h5238, h5239, h5240, h5782, h6, hc23, hc34, hlam, hphi]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5828 | h5828
          · linarith only [h5, h5238, h5239, h5240, h5773, h5777, h5828, h6, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5830 | h5830
            · linarith only [h5004, h5239, h5830, hc13, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5832 | h5832
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5833 | h5833
                · rcases h2bigk with h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c | h5834c
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [hlam, p5834_0]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    rcases p5834_3 (m.d 0 2) (by simp) with h5836 | h5836
                    · rcases p5834_3 (m.d 1 2) (by simp) with h5837 | h5837
                      · linarith only [h0, h5837, hlam]
                      · rcases p5834_3 (m.d 2 3) (by simp) with h5839 | h5839
                        · linarith only [h3, h5839, hlam]
                        · rcases p5834_3 (m.d 2 4) (by simp) with h5841 | h5841
                          · linarith only [h4, h5841, hlam]
                          · linarith only [h5240, h5777, h5832, h5841, hlam]
                    · linarith only [h0, h5836, hlam]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h4, h5239, h5773, h5777, h5832, hlam, p5834_2]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h0, h5239, h5773, h5777, h5832, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5834_1]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h0, h5239, h5240, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5834_1]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h0, hlam, p5834_0]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [hlam, p5834_0]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h0, h5, h5240, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5834_1]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h5240, h5832, hlam, p5834_1]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h5240, hlam, p5834_0]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h3, hlam, p5834_0]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h5239, hlam, p5834_0]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [hlam, p5834_0]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h5828, hlam, p5834_0]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h5830, hlam, p5834_0]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h4, hlam, p5834_0]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h0, h4, h5239, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5834_1]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    rcases p5834_3 (m.d 0 2) (by simp) with h5860 | h5860
                    · rcases p5834_3 (m.d 1 2) (by simp) with h5861 | h5861
                      · linarith only [h5240, h5777, h5832, h5861, hlam]
                      · linarith only [h5239, h5861, hlam]
                    · linarith only [h3, h5860, hlam]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [hlam, p5834_0]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h0, h4, h5239, h5240, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5834_1]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h5, hlam, p5834_0]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h0, h5, h5239, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5834_1]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    rcases p5834_3 (m.d 0 2) (by simp) with h5869 | h5869
                    · rcases p5834_3 (m.d 1 2) (by simp) with h5870 | h5870
                      · linarith only [h5240, h5870, hlam]
                      · linarith only [h5239, h5870, hlam]
                    · linarith only [h3, h5869, hlam]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [h5832, hlam, p5834_0]
                  · have p5834_0 := h5834c.1
                    have p5834_1 := h5834c.2.1
                    have p5834_2 := h5834c.2.2.1
                    have p5834_3 := h5834c.2.2.2
                    linarith only [hlam, p5834_0]
                · linarith only [h5833, h6, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
              · linarith only [h5238, h5239, h5240, h5832, h6, hc23, hc34, hlam, hphi]

end R2N4
