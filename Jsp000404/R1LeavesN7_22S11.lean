import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 0 2 5 (by decide) (by decide) with h4336 | h4336
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 0 2 5 (by decide) (by decide) with h6305 | h6305
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6306 | h6306
    · linarith only [h4334, h4335, h6306, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6308 | h6308
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6309 | h6309
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6310 | h6310
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6311 | h6311
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6312 | h6312
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6313 | h6313
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6314 | h6314
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6315 | h6315
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6316 | h6316
                      · linarith only [h3609, h4333, h4334, h6306, h6312, h6316, hc02, hc25, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6318 | h6318
                        · linarith only [h4334, h4335, h6310, h6313, h6316, h6318, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h6318, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h6315, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h6314, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6323 | h6323
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6324 | h6324
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6325 | h6325
                      · linarith only [h3609, h4333, h6312, h6313, h6325, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6327 | h6327
                        · linarith only [h4334, h4335, h6311, h6327, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h6327, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h4335, h6311, h6324, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h3609, h4333, h6312, h6323, hc25, hlam, hphi, u5elo3]
              · linarith only [h6312, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6333 | h6333
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6334 | h6334
                · linarith only [h3609, h4333, h6306, h6310, h6311, h6333, h6334, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6336 | h6336
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6337 | h6337
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6338 | h6338
                      · linarith only [h0, h4334, h6311, h6334, h6338, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6340 | h6340
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6341 | h6341
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6342 | h6342
                            · rcases h0bigk with h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [hlam, p6343_0]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h0, hlam, p6343_1]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h3609, hlam, p6343_0]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h4113, hlam, p6343_1]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h0, h6311, h6338, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6343_1]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h0, h6311, h6338, hc01, hc34, hlam, hphi, ht12, ht23, p6343_1]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [hlam, p6343_0]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h0, h6311, h6338, hc03, hc34, hlam, hphi, p6343_1]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h4335, hlam, p6343_1]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                rcases p6343_3 (m.d 0 1) (by simp) with h6353 | h6353
                                · linarith only [h0, h6353, hlam]
                                · linarith only [h4333, h6353, hlam]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h0, h4333, h4334, h6311, h6333, h6338, h6340, h6342, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6343_1]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h4334, hlam, p6343_1]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [hlam, p6343_0]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h6306, hlam, p6343_1]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                rcases p6343_3 (m.d 0 1) (by simp) with h6360 | h6360
                                · linarith only [h3609, h6360, hlam]
                                · linarith only [h4333, h6360, hlam]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                rcases p6343_3 (m.d 0 1) (by simp) with h6363 | h6363
                                · linarith only [h4113, h6363, hlam]
                                · rcases p6343_3 (m.d 0 2) (by simp) with h6365 | h6365
                                  · linarith only [h4335, h6365, hlam]
                                  · linarith only [h0, h6365, hlam]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h4113, h4334, h6311, h6338, hc23, hc34, hlam, hphi, p6343_1]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                rcases p6343_3 (m.d 0 1) (by simp) with h6369 | h6369
                                · linarith only [h4113, h6369, hlam]
                                · rcases p6343_3 (m.d 0 2) (by simp) with h6371 | h6371
                                  · linarith only [h4335, h6371, hlam]
                                  · linarith only [h4334, h6371, hlam]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [hlam, p6343_0]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                rcases p6343_3 (m.d 0 1) (by simp) with h6375 | h6375
                                · linarith only [h4113, h6375, hlam]
                                · linarith only [h4333, h6375, hlam]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h4333, hlam, p6343_0]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h6305, hlam, p6343_1]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h6308, hlam, p6343_0]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [h6309, hlam, p6343_1]
                              · have p6343_0 := h6343c.1
                                have p6343_1 := h6343c.2.1
                                have p6343_2 := h6343c.2.2.1
                                have p6343_3 := h6343c.2.2.2
                                linarith only [hlam, p6343_0]
                            · linarith only [h6311, h6338, h6342, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h3609, h4333, h6310, h6311, h6337, h6341, hlam]
                        · linarith only [h6340, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h4113, h6337, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h3609, h4333, h6333, h6336, hc25, hlam, hphi, u5elo3]
              · linarith only [h3609, h4333, h6310, h6333, hc15, hlam, hphi, u5elo2]
          · linarith only [h0, h4333, h4334, h6310, hc02, hc15, hlam, hphi, ht0b, ht5b]
        · linarith only [h6309, hc04, hlam, hphi, ht45, u5elo4]
      · linarith only [h3609, h4333, h6308, hc15, hlam, hphi, u5elo3]
  · linarith only [h4334, h6305, hc23, hlam, hphi, ht34, ht45, u5elo2]

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 0 2 4 (by decide) (by decide) with h4335 | h4335
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 0 2 4 (by decide) (by decide) with h6393 | h6393
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6394 | h6394
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6395 | h6395
      · rcases m.htr 0 3 5 (by decide) (by decide) with h6396 | h6396
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6397 | h6397
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6398 | h6398
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6399 | h6399
              · rcases m.htr 1 2 5 (by decide) (by decide) with h6400 | h6400
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6401 | h6401
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6402 | h6402
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6403 | h6403
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6404 | h6404
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6405 | h6405
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6406 | h6406
                            · linarith only [h4334, h6393, h6398, h6406, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h6406, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h4334, h6405, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h4113, h4333, h4334, h6393, h6395, h6404, hc03, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h6403, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h6402, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h4334, h6393, h6395, h6398, h6401, hlam]
                · linarith only [h4113, h4334, h6393, h6398, h6400, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h4113, h4333, h4334, h6393, h6398, h6399, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6416 | h6416
              · rcases m.htr 1 2 5 (by decide) (by decide) with h6417 | h6417
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6418 | h6418
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6419 | h6419
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6420 | h6420
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6421 | h6421
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6422 | h6422
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6423 | h6423
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6424 | h6424
                              · rcases h0bigk with h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [hlam, p6425_0]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h0, hlam, p6425_1]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h3609, hlam, p6425_0]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h4113, hlam, p6425_1]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h4113, h4333, h6398, h6416, h6417, h6422, h6424, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6425_1]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h0, h6398, hc01, hc23, hlam, hphi, ht12, p6425_1]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [hlam, p6425_0]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h4334, hlam, p6425_0]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h0, h4113, h4333, h6398, h6417, h6422, h6424, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6425_1]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  rcases p6425_3 (m.d 0 1) (by simp) with h6435 | h6435
                                  · linarith only [h0, h6435, hlam]
                                  · linarith only [h4333, h6435, hlam]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  rcases p6425_3 (m.d 0 1) (by simp) with h6438 | h6438
                                  · linarith only [h3609, h6438, hlam]
                                  · rcases p6425_3 (m.d 0 2) (by simp) with h6440 | h6440
                                    · linarith only [h4334, h6440, hlam]
                                    · linarith only [h0, h6440, hlam]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h3609, h6393, h6398, h6421, h6424, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6425_1]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [hlam, p6425_0]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  rcases p6425_3 (m.d 0 1) (by simp) with h6445 | h6445
                                  · linarith only [h3609, h6445, hlam]
                                  · rcases p6425_3 (m.d 0 2) (by simp) with h6447 | h6447
                                    · linarith only [h4334, h6447, hlam]
                                    · linarith only [h6393, h6447, hlam]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  rcases p6425_3 (m.d 0 1) (by simp) with h6450 | h6450
                                  · linarith only [h3609, h6450, hlam]
                                  · linarith only [h4333, h6450, hlam]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h4113, h4333, h6398, h6416, h6417, h6422, h6424, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6425_1]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h6393, hlam, p6425_0]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h6395, hlam, p6425_0]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [hlam, p6425_0]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  rcases p6425_3 (m.d 0 1) (by simp) with h6457 | h6457
                                  · linarith only [h4113, h6457, hlam]
                                  · linarith only [h4333, h6457, hlam]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h4333, hlam, p6425_0]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h6394, hlam, p6425_1]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h6396, hlam, p6425_0]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [h6397, hlam, p6425_1]
                                · have p6425_0 := h6425c.1
                                  have p6425_1 := h6425c.2.1
                                  have p6425_2 := h6425c.2.2.1
                                  have p6425_3 := h6425c.2.2.2
                                  linarith only [hlam, p6425_0]
                              · linarith only [h6424, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h4333, h6420, h6423, hc24, hlam, hphi, ht45, u5elo0]
                          · linarith only [h4113, h6398, h6416, h6422, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h4113, h4333, h6398, h6416, h6420, h6421, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h4113, h4333, h6417, h6420, hc25, hlam, hphi, u5elo4]
                    · linarith only [h3609, h6419, hc03, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h3609, h6395, h6418, hlam]
                · linarith only [h4113, h6416, h6417, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h6393, h6416, hlam]
          · linarith only [h6397, hc04, hlam, hphi, ht45, u5elo4]
        · linarith only [h4113, h4333, h4334, h6393, h6396, hc15, hlam, hphi, u5elo3]
      · linarith only [h4334, h6393, h6395, hlam]
    · linarith only [h4113, h4333, h6393, h6394, hc15, hlam, hphi, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6478 | h6478
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6479 | h6479
      · rcases m.htr 0 3 5 (by decide) (by decide) with h6480 | h6480
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6481 | h6481
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6482 | h6482
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6483 | h6483
              · rcases m.htr 1 2 5 (by decide) (by decide) with h6484 | h6484
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6485 | h6485
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6486 | h6486
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6487 | h6487
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6488 | h6488
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6489 | h6489
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6490 | h6490
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6491 | h6491
                              · rcases h0bigk with h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c | h6492c
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [hlam, p6492_0]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h0, hlam, p6492_1]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h3609, hlam, p6492_0]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h4113, hlam, p6492_1]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h0, h4333, h6393, h6482, h6484, h6488, h6489, h6491, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6492_1]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h6393, h6482, h6488, hc01, hc12, hlam, hphi, p6492_1]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [hlam, p6492_0]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h4334, hlam, p6492_0]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h6393, hlam, p6492_1]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h4333, h6393, h6482, h6484, h6488, h6489, h6491, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6492_1]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h4333, h4334, h6482, h6484, h6489, h6491, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6492_1]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h0, h4333, h4334, h6482, h6484, h6489, h6491, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6492_1]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [hlam, p6492_0]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h4113, h4333, h4334, h6482, h6484, h6489, h6491, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6492_1]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  rcases p6492_3 (m.d 0 1) (by simp) with h6507 | h6507
                                  · linarith only [h3609, h6507, hlam]
                                  · linarith only [h4333, h6507, hlam]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h4333, h6393, h6482, h6484, h6488, h6489, h6491, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6492_1]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h0, h4333, h6393, h6482, h6484, h6488, h6489, h6491, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6492_1]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h6479, hlam, p6492_0]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [hlam, p6492_0]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  rcases p6492_3 (m.d 0 1) (by simp) with h6514 | h6514
                                  · linarith only [h4113, h6514, hlam]
                                  · linarith only [h4333, h6514, hlam]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h4333, hlam, p6492_0]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h6478, hlam, p6492_1]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h6480, hlam, p6492_0]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [h6481, hlam, p6492_1]
                                · have p6492_0 := h6492c.1
                                  have p6492_1 := h6492c.2.1
                                  have p6492_2 := h6492c.2.2.1
                                  have p6492_3 := h6492c.2.2.2
                                  linarith only [hlam, p6492_0]
                              · linarith only [h6491, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h4333, h6393, h6487, h6490, hc04, hlam, hphi, ht45, u5elo0]
                          · linarith only [h0, h6393, h6488, h6489, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h4334, h6479, h6488, hlam]
                      · linarith only [h0, h6393, h6483, h6487, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h0, h4333, h6393, h6483, h6484, h6485, h6486, hc25, hlam, hphi, u5elo3]
                  · linarith only [h3609, h4333, h6479, h6484, h6485, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h4334, h6482, h6484, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h4333, h4334, h6482, h6483, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6531 | h6531
              · linarith only [h0, h4333, h6393, h6482, h6531, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h6533 | h6533
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6534 | h6534
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6535 | h6535
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6536 | h6536
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6537 | h6537
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6538 | h6538
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6539 | h6539
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6540 | h6540
                              · rcases h0bigk with h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c | h6541c
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [hlam, p6541_0]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [h0, hlam, p6541_1]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [h3609, hlam, p6541_0]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [h4113, hlam, p6541_1]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [h0, h6531, h6537, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6541_1]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [h0, h6531, h6537, hc01, hc23, hlam, hphi, ht12, p6541_1]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [hlam, p6541_0]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [h4334, hlam, p6541_0]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [h6393, hlam, p6541_1]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  rcases p6541_3 (m.d 0 1) (by simp) with h6551 | h6551
                                  · linarith only [h0, h6551, hlam]
                                  · linarith only [h4333, h6551, hlam]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  rcases p6541_3 (m.d 0 1) (by simp) with h6554 | h6554
                                  · linarith only [h3609, h6554, hlam]
                                  · rcases p6541_3 (m.d 0 2) (by simp) with h6556 | h6556
                                    · linarith only [h4334, h6556, hlam]
                                    · linarith only [h0, h6556, hlam]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  rcases p6541_3 (m.d 0 1) (by simp) with h6559 | h6559
                                  · linarith only [h3609, h6559, hlam]
                                  · rcases p6541_3 (m.d 0 2) (by simp) with h6561 | h6561
                                    · linarith only [h4334, h6561, hlam]
                                    · rcases p6541_3 (m.d 0 3) (by simp) with h6563 | h6563
                                      · rcases p6541_3 (m.d 0 4) (by simp) with h6564 | h6564
                                        · linarith only [h6479, h6564, hlam]
                                        · linarith only [h6393, h6564, hlam]
                                      · linarith only [h4334, h6563, hlam]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [hlam, p6541_0]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  rcases p6541_3 (m.d 0 1) (by simp) with h6569 | h6569
                                  · linarith only [h3609, h6569, hlam]
                                  · rcases p6541_3 (m.d 0 2) (by simp) with h6571 | h6571
                                    · linarith only [h4334, h6571, hlam]
                                    · rcases p6541_3 (m.d 0 3) (by simp) with h6573 | h6573
                                      · rcases p6541_3 (m.d 0 4) (by simp) with h6574 | h6574
                                        · linarith only [h6479, h6574, hlam]
                                        · rcases p6541_3 (m.d 0 5) (by simp) with h6576 | h6576
                                          · linarith only [h6480, h6576, hlam]
                                          · rcases h0emin with h6578 | h6578 | h6578 | h6578 | h6578
                                            · linarith only [h0, h6531, h6537, h6578, hc23, hlam, ht01, ht12]
                                            · linarith only [h3609, h6393, h6482, h6578, hc23, hlam, ht01, ht12, p6541_1]
                                            · rcases h2bigk with h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c | h6581c
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [hlam, p6581_0]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h0, hlam, p6581_1]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h4334, hlam, p6581_0]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h6393, hlam, p6581_0]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h3609, h6393, h6482, h6538, h6540, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6541_1, p6581_1]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h0, h6531, h6537, hc01, hc23, hlam, hphi, ht12, p6581_1]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [hlam, p6581_0]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h6482, hlam, p6581_0]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h6531, hlam, p6581_0]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                rcases p6581_3 (m.d 0 2) (by simp) with h6591 | h6591
                                                · linarith only [h0, h6591, hlam]
                                                · linarith only [h6478, h6591, hlam]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                rcases p6581_3 (m.d 0 2) (by simp) with h6594 | h6594
                                                · linarith only [h6594, hlam, p6581_0]
                                                · rcases p6581_3 (m.d 1 2) (by simp) with h6596 | h6596
                                                  · linarith only [h6482, h6596, hlam]
                                                  · linarith only [h0, h6596, hlam]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h0, h4333, h6533, h6538, h6540, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6581_1]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [hlam, p6581_0]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h0, h4333, h6393, h6533, h6538, h6540, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6581_1]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h3609, h4113, h4333, h6482, h6533, hlam, p6541_1, p6581_2]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                rcases p6581_3 (m.d 0 2) (by simp) with h6603 | h6603
                                                · linarith only [h6603, hlam, p6581_0]
                                                · rcases p6581_3 (m.d 1 2) (by simp) with h6605 | h6605
                                                  · linarith only [h6531, h6605, hlam]
                                                  · linarith only [h0, h6605, hlam]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h0, h4333, h6533, h6538, h6540, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6581_1]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h6537, hlam, p6581_1]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [hlam, p6581_0]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h0, h4333, h6531, h6533, hlam, p6581_2]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h6478, hlam, p6581_0]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h6533, hlam, p6581_0]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h6538, hlam, p6581_1]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [h6539, hlam, p6581_0]
                                              · have p6581_0 := h6581c.1
                                                have p6581_1 := h6581c.2.1
                                                have p6581_2 := h6581c.2.2.1
                                                have p6581_3 := h6581c.2.2.2
                                                linarith only [hlam, p6581_0]
                                            · linarith only [h6578, hc03, hlam, p6541_1]
                                            · linarith only [h0, h3609, h4333, h6393, h6482, h6533, h6538, h6540, h6578, hc23, hc45, hlam, hphi, ht01, ht12, p6541_1, u5elo0]
                                      · linarith only [h6479, h6573, hlam]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  rcases p6541_3 (m.d 0 1) (by simp) with h6620 | h6620
                                  · linarith only [h3609, h6620, hlam]
                                  · linarith only [h4333, h6620, hlam]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  rcases p6541_3 (m.d 0 1) (by simp) with h6623 | h6623
                                  · linarith only [h4113, h6623, hlam]
                                  · rcases p6541_3 (m.d 0 2) (by simp) with h6625 | h6625
                                    · linarith only [h6393, h6625, hlam]
                                    · linarith only [h0, h6625, hlam]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  rcases p6541_3 (m.d 0 1) (by simp) with h6628 | h6628
                                  · linarith only [h4113, h6628, hlam]
                                  · rcases p6541_3 (m.d 0 2) (by simp) with h6630 | h6630
                                    · linarith only [h6393, h6630, hlam]
                                    · rcases p6541_3 (m.d 0 3) (by simp) with h6632 | h6632
                                      · rcases p6541_3 (m.d 0 4) (by simp) with h6633 | h6633
                                        · rcases p6541_3 (m.d 0 5) (by simp) with h6634 | h6634
                                          · linarith only [h6481, h6634, hlam]
                                          · rcases h0emin with h6636 | h6636 | h6636 | h6636 | h6636
                                            · linarith only [h0, h6636, hc04, hlam, p6541_1]
                                            · linarith only [h6636, hc04, hlam, p6541_1]
                                            · rcases h2bigk with h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [hlam, p6639_0]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h0, hlam, p6639_1]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h4334, hlam, p6639_0]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h6393, hlam, p6639_0]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h3609, h6479, h6482, h6538, h6540, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6541_1, p6639_1]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h0, h6482, hc01, hc23, hlam, hphi, ht12, p6639_1]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [hlam, p6639_0]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h6482, hlam, p6639_0]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h6531, hlam, p6639_0]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                rcases p6639_3 (m.d 0 2) (by simp) with h6649 | h6649
                                                · linarith only [h0, h6649, hlam]
                                                · linarith only [h6478, h6649, hlam]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                rcases p6639_3 (m.d 0 2) (by simp) with h6652 | h6652
                                                · linarith only [h6652, hlam, p6639_0]
                                                · rcases p6639_3 (m.d 1 2) (by simp) with h6654 | h6654
                                                  · linarith only [h6482, h6654, hlam]
                                                  · linarith only [h0, h6654, hlam]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h0, h4333, h6533, h6538, h6540, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6639_1]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [hlam, p6639_0]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h0, h4333, h6393, h6533, h6538, h6540, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6639_1]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h0, h3609, h4333, h6479, h6482, h6533, hlam, p6541_1, p6639_2]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                rcases p6639_3 (m.d 0 2) (by simp) with h6661 | h6661
                                                · linarith only [h6661, hlam, p6639_0]
                                                · rcases p6639_3 (m.d 1 2) (by simp) with h6663 | h6663
                                                  · linarith only [h6531, h6663, hlam]
                                                  · linarith only [h0, h6663, hlam]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h0, h4333, h6533, h6538, h6540, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6639_1]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h6537, hlam, p6639_1]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [hlam, p6639_0]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h0, h4333, h6393, h6533, hlam, p6541_1, p6639_2]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h6478, hlam, p6639_0]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h6533, hlam, p6639_0]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h6538, hlam, p6639_1]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [h6539, hlam, p6639_0]
                                              · have p6639_0 := h6639c.1
                                                have p6639_1 := h6639c.2.1
                                                have p6639_2 := h6639c.2.2.1
                                                have p6639_3 := h6639c.2.2.2
                                                linarith only [hlam, p6639_0]
                                            · rcases h2bigk with h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [hlam, p6675_0]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h0, hlam, p6675_1]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h4334, hlam, p6675_0]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h6393, hlam, p6675_0]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h6479, h6538, h6540, hc03, hc45, hlam, hphi, ht0b, ht5b, p6541_1, p6675_1]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h0, h4333, h6482, h6533, h6538, h6540, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6675_1]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [hlam, p6675_0]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h6482, hlam, p6675_0]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h6531, hlam, p6675_0]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                rcases p6675_3 (m.d 0 2) (by simp) with h6685 | h6685
                                                · linarith only [h0, h6685, hlam]
                                                · linarith only [h6478, h6685, hlam]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                rcases p6675_3 (m.d 0 2) (by simp) with h6688 | h6688
                                                · linarith only [h6688, hlam, p6675_0]
                                                · rcases p6675_3 (m.d 1 2) (by simp) with h6690 | h6690
                                                  · linarith only [h6482, h6690, hlam]
                                                  · linarith only [h0, h6690, hlam]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h0, h4333, h6533, h6538, h6540, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6675_1]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [hlam, p6675_0]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h0, h4333, h6393, h6533, h6538, h6540, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6675_1]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h0, h3609, h4333, h6479, h6482, h6533, hlam, p6541_1, p6675_2]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                rcases p6675_3 (m.d 0 2) (by simp) with h6697 | h6697
                                                · linarith only [h6697, hlam, p6675_0]
                                                · rcases p6675_3 (m.d 1 2) (by simp) with h6699 | h6699
                                                  · linarith only [h6531, h6699, hlam]
                                                  · linarith only [h0, h6699, hlam]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h0, h6537, hc01, hc23, hlam, hphi, ht12, p6675_1]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h6537, hlam, p6675_1]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [hlam, p6675_0]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h0, h4333, h6393, h6533, hlam, p6541_1, p6675_2]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h6478, hlam, p6675_0]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h6533, hlam, p6675_0]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h6538, hlam, p6675_1]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [h6539, hlam, p6675_0]
                                              · have p6675_0 := h6675c.1
                                                have p6675_1 := h6675c.2.1
                                                have p6675_2 := h6675c.2.2.1
                                                have p6675_3 := h6675c.2.2.2
                                                linarith only [hlam, p6675_0]
                                            · linarith only [h6636, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                        · linarith only [h6393, h6633, hlam]
                                      · linarith only [h4334, h6632, hlam]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [h6479, hlam, p6541_0]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [hlam, p6541_0]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  rcases p6541_3 (m.d 0 1) (by simp) with h6716 | h6716
                                  · linarith only [h4113, h6716, hlam]
                                  · linarith only [h4333, h6716, hlam]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [h4333, hlam, p6541_0]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [h6478, hlam, p6541_1]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [h6480, hlam, p6541_0]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [h6481, hlam, p6541_1]
                                · have p6541_0 := h6541c.1
                                  have p6541_1 := h6541c.2.1
                                  have p6541_2 := h6541c.2.2.1
                                  have p6541_3 := h6541c.2.2.2
                                  linarith only [hlam, p6541_0]
                              · linarith only [h6540, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h4333, h6531, h6536, h6539, hlam]
                          · linarith only [h0, h6531, h6537, h6538, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h6482, h6537, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h4333, h6531, h6533, h6536, hc25, hlam, hphi, u5elo4]
                    · linarith only [h0, h4333, h6531, h6533, h6534, h6535, hc25, hlam, hphi, u5elo3]
                  · linarith only [h3609, h6479, h6534, hlam]
                · linarith only [h0, h6533, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h6481, hc04, hlam, hphi, ht45, u5elo4]
        · linarith only [h6480, hc03, hlam, hphi, ht34, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h6734 | h6734
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6735 | h6735
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6736 | h6736
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6737 | h6737
              · rcases m.htr 1 2 5 (by decide) (by decide) with h6738 | h6738
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6739 | h6739
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6740 | h6740
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6741 | h6741
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6742 | h6742
                        · linarith only [h0, h4333, h4334, h6479, h6736, h6738, h6742, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h4333, h4334, h6738, h6739, h6742, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h6741, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h6740, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6747 | h6747
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6748 | h6748
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6749 | h6749
                        · linarith only [h6736, h6739, h6749, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6751 | h6751
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6752 | h6752
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6753 | h6753
                              · rcases h0bigk with h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c | h6754c
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [hlam, p6754_0]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h0, hlam, p6754_1]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h3609, hlam, p6754_0]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h4113, hlam, p6754_1]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h0, h4334, h6736, h6739, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6754_1]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h4334, h6736, h6739, hc01, hc34, hlam, hphi, ht12, ht23, p6754_1]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [hlam, p6754_0]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h4334, hlam, p6754_0]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h6393, hlam, p6754_1]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h4333, h4334, h6736, h6738, h6739, h6751, h6753, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6754_1]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h3609, h4333, h6738, h6739, h6751, h6753, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6754_1]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h4334, h6736, h6739, hc02, hc34, hlam, hphi, ht23, p6754_1]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [hlam, p6754_0]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h6479, hlam, p6754_1]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  rcases p6754_3 (m.d 0 1) (by simp) with h6769 | h6769
                                  · linarith only [h3609, h6769, hlam]
                                  · linarith only [h4333, h6769, hlam]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h4333, h6393, h6737, h6738, h6751, h6753, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6754_1]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h0, h4333, h6393, h6737, h6738, h6751, h6753, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6754_1]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h0, h4333, h4334, h6393, h6737, h6738, h6751, h6753, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6754_1]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [hlam, p6754_0]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  rcases p6754_3 (m.d 0 1) (by simp) with h6776 | h6776
                                  · linarith only [h4113, h6776, hlam]
                                  · linarith only [h4333, h6776, hlam]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h4333, hlam, p6754_0]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h6478, hlam, p6754_1]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h6734, hlam, p6754_0]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [h6735, hlam, p6754_1]
                                · have p6754_0 := h6754c.1
                                  have p6754_1 := h6754c.2.1
                                  have p6754_2 := h6754c.2.2.1
                                  have p6754_3 := h6754c.2.2.2
                                  linarith only [hlam, p6754_0]
                              · linarith only [h6736, h6739, h6753, hc23, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h0, h4333, h4334, h6393, h6736, h6739, h6748, h6752, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h4334, h6751, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h4334, h6736, h6739, h6748, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h0, h4334, h6736, h6747, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h4334, h6736, h6738, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h4334, h6736, h6737, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6791 | h6791
              · linarith only [h0, h4333, h6393, h6736, h6791, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h6793 | h6793
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6794 | h6794
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6795 | h6795
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6796 | h6796
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6797 | h6797
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6798 | h6798
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6799 | h6799
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6800 | h6800
                              · rcases h0bigk with h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c | h6801c
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [hlam, p6801_0]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h0, hlam, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h3609, hlam, p6801_0]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h4113, hlam, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h0, h6791, h6797, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h0, h6791, h6797, hc01, hc23, hlam, hphi, ht12, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [hlam, p6801_0]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h4334, hlam, p6801_0]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h6393, hlam, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h4333, h4334, h6479, h6736, h6793, h6794, h6798, h6800, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h4333, h6479, h6736, h6793, h6794, h6798, h6800, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h6479, h6736, h6794, hc02, hc23, hlam, hphi, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [hlam, p6801_0]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h6479, hlam, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h4333, h6479, h6736, h6793, h6794, h6798, h6800, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h4333, h6479, h6736, h6793, h6794, h6798, h6800, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h0, h4333, h6479, h6736, h6793, h6794, h6798, h6800, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h3609, h4333, h6479, h6736, h6793, h6794, h6798, h6800, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [hlam, p6801_0]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  rcases p6801_3 (m.d 0 1) (by simp) with h6821 | h6821
                                  · linarith only [h4113, h6821, hlam]
                                  · linarith only [h4333, h6821, hlam]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h4333, hlam, p6801_0]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h6478, hlam, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h6734, hlam, p6801_0]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [h6735, hlam, p6801_1]
                                · have p6801_0 := h6801c.1
                                  have p6801_1 := h6801c.2.1
                                  have p6801_2 := h6801c.2.2.1
                                  have p6801_3 := h6801c.2.2.2
                                  linarith only [hlam, p6801_0]
                              · linarith only [h6479, h6800, hc04, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h4333, h4334, h6479, h6736, h6791, h6794, h6796, h6799, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h4334, h6479, h6736, h6794, h6798, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h6736, h6794, h6797, hlam]
                      · linarith only [h6796, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h0, h4333, h4334, h6479, h6793, h6794, h6795, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6835 | h6835
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6836 | h6836
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6837 | h6837
                        · linarith only [h0, h6736, h6794, h6837, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h4333, h6736, h6793, h6837, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h6836, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h0, h4333, h6736, h6793, h6835, hc25, hlam, hphi, u5elo3]
                · linarith only [h0, h4333, h6793, hc15, hlam, hphi, u5elo2]
          · linarith only [h0, h4333, h4334, h6479, h6735, hc15, hlam, hphi, u5elo4]
        · linarith only [h0, h4333, h4334, h6734, hc15, hlam, hphi, u5elo3]
    · linarith only [h0, h4333, h6478, hc15, hlam, hphi, u5elo2]

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 0 2 3 (by decide) (by decide) with h4334 | h4334
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x1 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334

set_option maxHeartbeats 5028000 in
set_option maxHeartbeats 5028000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s6 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  rcases m.htr 0 1 5 (by decide) (by decide) with h4333 | h4333
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7 m hb0 hb2 hb3 hb5 h0 h3609 h4113 h4333
  · linarith only [h4333, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 5468000 in
set_option maxHeartbeats 5468000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s5 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  rcases m.htr 0 1 4 (by decide) (by decide) with h4113 | h4113
  · rcases m.htr 0 1 5 (by decide) (by decide) with h4114 | h4114
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4115 | h4115
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4116 | h4116
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4117 | h4117
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4118 | h4118
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4119 | h4119
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4120 | h4120
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4121 | h4121
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4122 | h4122
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4123 | h4123
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4124 | h4124
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4125 | h4125
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4126 | h4126
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4127 | h4127
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4128 | h4128
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4129 | h4129
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4130 | h4130
                                    · rcases h0bigk with h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [hlam, p4131_0]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [h0, hlam, p4131_1]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [h3609, hlam, p4131_0]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [h3609, h4113, h4122, h4127, h4130, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p4131_1]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        rcases p4131_3 (m.d 0 1) (by simp) with h4136 | h4136
                                        · rcases p4131_3 (m.d 0 2) (by simp) with h4137 | h4137
                                          · rcases p4131_3 (m.d 0 3) (by simp) with h4138 | h4138
                                            · rcases p4131_3 (m.d 0 4) (by simp) with h4139 | h4139
                                              · linarith only [h4113, h4139, hlam]
                                              · linarith only [h4120, h4139, hlam]
                                            · linarith only [h4119, h4138, hlam]
                                          · linarith only [h4117, h4137, hlam]
                                        · linarith only [h4114, h4136, hlam]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [h0, h4113, h4122, h4127, h4130, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4131_1]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [hlam, p4131_0]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [h0, h3609, h4113, h4122, h4127, h4130, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4131_1]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        rcases p4131_3 (m.d 0 1) (by simp) with h4148 | h4148
                                        · linarith only [h0, h4148, hlam]
                                        · linarith only [h4113, h4148, hlam]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        rcases p4131_3 (m.d 0 1) (by simp) with h4151 | h4151
                                        · linarith only [h0, h4151, hlam]
                                        · linarith only [h4114, h4151, hlam]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [h4113, h4122, h4127, h4130, hc03, hc45, hlam, hphi, ht0b, ht5b, p4131_1]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [h4115, hlam, p4131_1]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [hlam, p4131_0]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        rcases p4131_3 (m.d 0 1) (by simp) with h4157 | h4157
                                        · linarith only [h3609, h4157, hlam]
                                        · linarith only [h4113, h4157, hlam]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        rcases p4131_3 (m.d 0 1) (by simp) with h4160 | h4160
                                        · linarith only [h3609, h4160, hlam]
                                        · linarith only [h4114, h4160, hlam]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [h4113, hlam, p4131_0]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [h4116, hlam, p4131_0]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [h4118, hlam, p4131_0]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [hlam, p4131_0]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        rcases p4131_3 (m.d 0 1) (by simp) with h4167 | h4167
                                        · rcases p4131_3 (m.d 0 2) (by simp) with h4168 | h4168
                                          · rcases p4131_3 (m.d 0 3) (by simp) with h4169 | h4169
                                            · rcases p4131_3 (m.d 0 4) (by simp) with h4170 | h4170
                                              · rcases p4131_3 (m.d 0 5) (by simp) with h4171 | h4171
                                                · linarith only [h4120, h4171, hlam]
                                                · rcases h0emin with h4173 | h4173 | h4173 | h4173 | h4173
                                                  · linarith only [h0, h4173, hc12, hlam, ht01]
                                                  · rcases h2bigk with h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c | h4175c
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [hlam, p4175_0]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h0, hlam, p4175_1]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h0, h4127, h4130, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4175_1]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      rcases p4175_3 (m.d 0 2) (by simp) with h4179 | h4179
                                                      · rcases p4175_3 (m.d 1 2) (by simp) with h4180 | h4180
                                                        · rcases p4175_3 (m.d 2 3) (by simp) with h4181 | h4181
                                                          · linarith only [h4115, h4181, hlam]
                                                          · linarith only [h4127, h4181, hlam]
                                                        · linarith only [h4122, h4180, hlam]
                                                      · linarith only [h4179, hlam, p4175_0]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      rcases p4175_3 (m.d 0 2) (by simp) with h4186 | h4186
                                                      · rcases p4175_3 (m.d 1 2) (by simp) with h4187 | h4187
                                                        · rcases p4175_3 (m.d 2 3) (by simp) with h4188 | h4188
                                                          · linarith only [h4115, h4188, hlam]
                                                          · linarith only [h4128, h4188, hlam]
                                                        · linarith only [h4123, h4187, hlam]
                                                      · linarith only [h4186, hlam, p4175_0]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h4173, hc12, hlam, ht01, p4175_1]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [hlam, p4175_0]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h4127, h4130, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4175_1]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      rcases p4175_3 (m.d 0 2) (by simp) with h4196 | h4196
                                                      · linarith only [h0, h4196, hlam]
                                                      · linarith only [h4116, h4196, hlam]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h3609, h4113, h4114, h4121, h4123, hlam, p4131_1, p4175_2]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h4115, hlam, p4175_0]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h4121, hlam, p4175_0]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [hlam, p4175_0]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h0, h4115, h4129, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4175_1]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      rcases p4175_3 (m.d 0 2) (by simp) with h4204 | h4204
                                                      · rcases p4175_3 (m.d 1 2) (by simp) with h4205 | h4205
                                                        · rcases p4175_3 (m.d 2 3) (by simp) with h4206 | h4206
                                                          · rcases p4175_3 (m.d 2 4) (by simp) with h4207 | h4207
                                                            · linarith only [h4127, h4207, hlam]
                                                            · linarith only [h4129, h4207, hlam]
                                                          · linarith only [h4128, h4206, hlam]
                                                        · linarith only [h4123, h4205, hlam]
                                                      · linarith only [h4117, h4204, hlam]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h4116, hlam, p4175_0]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h4122, hlam, p4175_0]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h4127, hlam, p4175_1]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [hlam, p4175_0]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h0, h4113, h4122, h4128, h4130, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4175_1]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h4117, hlam, p4175_0]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h4123, hlam, p4175_0]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h4128, hlam, p4175_1]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [h4129, hlam, p4175_0]
                                                    · have p4175_0 := h4175c.1
                                                      have p4175_1 := h4175c.2.1
                                                      have p4175_2 := h4175c.2.2.1
                                                      have p4175_3 := h4175c.2.2.2
                                                      linarith only [hlam, p4175_0]
                                                  · rcases h2bigk with h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c | h4223c
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [hlam, p4223_0]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h0, hlam, p4223_1]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h0, h4127, h4130, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4223_1]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      rcases p4223_3 (m.d 0 2) (by simp) with h4227 | h4227
                                                      · rcases p4223_3 (m.d 1 2) (by simp) with h4228 | h4228
                                                        · rcases p4223_3 (m.d 2 3) (by simp) with h4229 | h4229
                                                          · linarith only [h4115, h4229, hlam]
                                                          · linarith only [h4127, h4229, hlam]
                                                        · linarith only [h4122, h4228, hlam]
                                                      · linarith only [h4227, hlam, p4223_0]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      rcases p4223_3 (m.d 0 2) (by simp) with h4234 | h4234
                                                      · rcases p4223_3 (m.d 1 2) (by simp) with h4235 | h4235
                                                        · rcases p4223_3 (m.d 2 3) (by simp) with h4236 | h4236
                                                          · linarith only [h4115, h4236, hlam]
                                                          · linarith only [h4128, h4236, hlam]
                                                        · linarith only [h4123, h4235, hlam]
                                                      · linarith only [h4234, hlam, p4223_0]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h4115, h4173, hc12, hlam, ht01, p4223_1]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [hlam, p4223_0]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h4127, h4130, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4223_1]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      rcases p4223_3 (m.d 0 2) (by simp) with h4244 | h4244
                                                      · linarith only [h0, h4244, hlam]
                                                      · linarith only [h4116, h4244, hlam]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h3609, h4113, h4114, h4121, h4123, hlam, p4131_1, p4223_2]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h4115, hlam, p4223_0]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h4121, hlam, p4223_0]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [hlam, p4223_0]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h4115, h4127, h4130, hc02, hc45, hlam, hphi, ht0b, ht5b, p4223_1]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      rcases p4223_3 (m.d 0 2) (by simp) with h4252 | h4252
                                                      · rcases p4223_3 (m.d 1 2) (by simp) with h4253 | h4253
                                                        · rcases p4223_3 (m.d 2 3) (by simp) with h4254 | h4254
                                                          · rcases p4223_3 (m.d 2 4) (by simp) with h4255 | h4255
                                                            · linarith only [h4127, h4255, hlam]
                                                            · linarith only [h4129, h4255, hlam]
                                                          · linarith only [h4128, h4254, hlam]
                                                        · linarith only [h4123, h4253, hlam]
                                                      · linarith only [h4117, h4252, hlam]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h4116, hlam, p4223_0]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h4122, hlam, p4223_0]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h4127, hlam, p4223_1]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [hlam, p4223_0]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h3609, h4113, h4122, h4128, h4130, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p4223_1]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h4117, hlam, p4223_0]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h4123, hlam, p4223_0]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h4128, hlam, p4223_1]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [h4129, hlam, p4223_0]
                                                    · have p4223_0 := h4223c.1
                                                      have p4223_1 := h4223c.2.1
                                                      have p4223_2 := h4223c.2.2.1
                                                      have p4223_3 := h4223c.2.2.2
                                                      linarith only [hlam, p4223_0]
                                                  · linarith only [h3609, h4113, h4173, hc13, hlam, ht01]
                                                  · linarith only [h4173, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                              · linarith only [h4120, h4170, hlam]
                                            · linarith only [h4119, h4169, hlam]
                                          · linarith only [h4117, h4168, hlam]
                                        · linarith only [h4114, h4167, hlam]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [h4114, hlam, p4131_0]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [h4117, hlam, p4131_1]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [h4119, hlam, p4131_0]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [h4120, hlam, p4131_1]
                                      · have p4131_0 := h4131c.1
                                        have p4131_1 := h4131c.2.1
                                        have p4131_2 := h4131c.2.2.1
                                        have p4131_3 := h4131c.2.2.2
                                        linarith only [hlam, p4131_0]
                                    · linarith only [h4130, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h3609, h4113, h4121, h4126, h4129, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h4128, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4285 | h4285
                                · linarith only [h3609, h4113, h4121, h4124, h4127, h4285, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h4285, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h4126, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h3609, h4125, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h3609, h4118, h4124, hlam]
                      · linarith only [h0, h4123, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h3609, h4113, h4116, h4121, h4122, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h4115, h4121, hlam]
                · linarith only [h4120, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h4119, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h3609, h4113, h4118, hlam]
          · linarith only [h4117, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3609, h4113, h4115, h4116, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4299 | h4299
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4300 | h4300
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4301 | h4301
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4302 | h4302
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4303 | h4303
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4304 | h4304
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4305 | h4305
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4306 | h4306
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4307 | h4307
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4308 | h4308
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4309 | h4309
                            · linarith only [h0, h4113, h4115, h4304, h4309, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h4309, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h4113, h4115, h4304, h4305, h4308, hc24, hlam, hphi, ht45, u5elo3]
                        · linarith only [h0, h4113, h4115, h4301, h4304, h4305, h4307, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h4113, h4115, h4304, h4305, h4306, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h4113, h4115, h4304, h4305, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4316 | h4316
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4317 | h4317
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4318 | h4318
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4319 | h4319
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4320 | h4320
                            · linarith only [h0, h4113, h4304, h4320, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h4320, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h3609, h4319, hc03, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h4113, h4301, h4304, h4316, h4318, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h4113, h4316, h4317, hc24, hlam, hphi, ht45, u5elo2]
                    · linarith only [h0, h4113, h4299, h4316, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h4303, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h4302, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h0, h4113, h4115, h4301, hlam]
          · linarith only [h0, h4300, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h4113, h4299, hlam]
    · linarith only [h4113, h4114, hc14, hlam, hphi, ht45, u5elo1]
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s6 m hb0 hb2 hb3 hb5 h0 h3609 h4113

end R2N4
