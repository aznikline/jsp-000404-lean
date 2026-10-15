import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 16094000 in
set_option maxHeartbeats 16094000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x1_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5823 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h6193 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h6194 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h6195 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 5 (by decide) (by decide) with h6196 | h6196
  · rcases m.htr 1 3 4 (by decide) (by decide) with h6197 | h6197
    · linarith only [h1, h6197, h7, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h6199 | h6199
      · linarith only [h1, h5823, h6199, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h6201 | h6201
        · rcases m.htr 2 3 4 (by decide) (by decide) with h6202 | h6202
          · linarith only [h4, h6202, h7, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h6204 | h6204
            · linarith only [h1, h5823, h6194, h6204, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6206 | h6206
              · rcases m.htr 3 4 5 (by decide) (by decide) with h6207 | h6207
                · rcases h1bigk with h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c | h6208c
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [hlam, p6208_0]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [h6195, h6206, hc01, hc45, hlam, hphi, ht0b, ht5b, p6208_1]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    rcases p6208_3 (m.d 0 1) (by simp) with h6211 | h6211
                    · rcases p6208_3 (m.d 1 2) (by simp) with h6212 | h6212
                      · linarith only [h0, h6212, hlam]
                      · linarith only [h6194, h6212, hlam]
                    · linarith only [h6211, hlam, p6208_0]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    rcases p6208_3 (m.d 0 1) (by simp) with h6216 | h6216
                    · rcases p6208_3 (m.d 1 2) (by simp) with h6217 | h6217
                      · linarith only [h0, h6217, hlam]
                      · linarith only [h6195, h6217, hlam]
                    · linarith only [h6216, hlam, p6208_0]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    rcases p6208_3 (m.d 0 1) (by simp) with h6221 | h6221
                    · rcases p6208_3 (m.d 1 2) (by simp) with h6222 | h6222
                      · linarith only [h0, h6222, hlam]
                      · linarith only [h6196, h6222, hlam]
                    · linarith only [h6221, hlam, p6208_0]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [h0, hlam, p6208_0]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [hlam, p6208_0]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    rcases p6208_3 (m.d 0 1) (by simp) with h6228 | h6228
                    · rcases p6208_3 (m.d 1 2) (by simp) with h6229 | h6229
                      · rcases p6208_3 (m.d 1 3) (by simp) with h6230 | h6230
                        · linarith only [h6194, h6230, hlam]
                        · rcases p6208_3 (m.d 1 4) (by simp) with h6232 | h6232
                          · linarith only [h6195, h6232, hlam]
                          · linarith only [h6197, h6232, hlam]
                      · linarith only [h6194, h6229, hlam]
                    · linarith only [h1, h6228, hlam]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [h0, h6195, h6206, hc01, hc45, hlam, hphi, ht0b, ht5b, p6208_1]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    rcases p6208_3 (m.d 0 1) (by simp) with h6238 | h6238
                    · rcases p6208_3 (m.d 1 2) (by simp) with h6239 | h6239
                      · rcases p6208_3 (m.d 1 3) (by simp) with h6240 | h6240
                        · linarith only [h6194, h6240, hlam]
                        · rcases p6208_3 (m.d 1 4) (by simp) with h6242 | h6242
                          · linarith only [h6195, h6242, hlam]
                          · linarith only [h6201, h6242, hlam]
                      · linarith only [h6196, h6239, hlam]
                    · linarith only [h3, h6238, hlam]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [h1, hlam, p6208_0]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [h6194, hlam, p6208_1]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [hlam, p6208_0]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [h6197, hlam, p6208_1]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [h6199, hlam, p6208_1]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [h2, hlam, p6208_0]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [h6195, hlam, p6208_1]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    rcases p6208_3 (m.d 0 1) (by simp) with h6254 | h6254
                    · rcases p6208_3 (m.d 1 2) (by simp) with h6255 | h6255
                      · rcases p6208_3 (m.d 1 3) (by simp) with h6256 | h6256
                        · linarith only [h6197, h6256, hlam]
                        · rcases p6208_3 (m.d 1 4) (by simp) with h6258 | h6258
                          · rcases p6208_3 (m.d 1 5) (by simp) with h6259 | h6259
                            · linarith only [h6201, h6259, hlam]
                            · linarith only [h6199, h6259, hlam]
                          · linarith only [h6197, h6258, hlam]
                      · linarith only [h6194, h6255, hlam]
                    · linarith only [h1, h6254, hlam]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [hlam, p6208_0]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    rcases p6208_3 (m.d 0 1) (by simp) with h6266 | h6266
                    · rcases p6208_3 (m.d 1 2) (by simp) with h6267 | h6267
                      · rcases p6208_3 (m.d 1 3) (by simp) with h6268 | h6268
                        · linarith only [h6197, h6268, hlam]
                        · rcases p6208_3 (m.d 1 4) (by simp) with h6270 | h6270
                          · rcases p6208_3 (m.d 1 5) (by simp) with h6271 | h6271
                            · linarith only [h6201, h6271, hlam]
                            · rcases h3bigk with h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c | h6273c
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [h5823, h6194, h6207, hc23, hc34, hlam, hphi, p6273_1]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [h5823, h6207, hc23, hc34, hlam, hphi, p6273_1]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [h7, hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [h5823, hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [h1, hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [h2, h6199, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6208_1, p6273_1]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [h6197, hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [h6199, hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [h4, hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [h6194, hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [h6202, hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [h6204, hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                rcases p6273_3 (m.d 0 3) (by simp) with h6289 | h6289
                                · linarith only [h6289, hlam, p6273_0]
                                · rcases p6273_3 (m.d 1 3) (by simp) with h6291 | h6291
                                  · linarith only [h6197, h6291, hlam]
                                  · rcases p6273_3 (m.d 2 3) (by simp) with h6293 | h6293
                                    · linarith only [h6202, h6293, hlam]
                                    · rcases p6273_3 (m.d 3 4) (by simp) with h6295 | h6295
                                      · rcases p6273_3 (m.d 3 5) (by simp) with h6296 | h6296
                                        · linarith only [h6207, h6296, hlam]
                                        · linarith only [h5823, h6296, hlam]
                                      · linarith only [h6295, hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                rcases p6273_3 (m.d 0 3) (by simp) with h6300 | h6300
                                · linarith only [h6300, h7, hlam]
                                · linarith only [h1, h6300, hlam]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                rcases p6273_3 (m.d 0 3) (by simp) with h6303 | h6303
                                · linarith only [h6303, h7, hlam]
                                · linarith only [h4, h6303, hlam]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [h5823, hc03, hc34, hlam, hphi, p6273_1]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                rcases p6273_3 (m.d 0 3) (by simp) with h6308 | h6308
                                · linarith only [h6308, hlam, p6273_0]
                                · rcases p6273_3 (m.d 1 3) (by simp) with h6310 | h6310
                                  · linarith only [h6199, h6310, hlam]
                                  · rcases p6273_3 (m.d 2 3) (by simp) with h6312 | h6312
                                    · linarith only [h6204, h6312, hlam]
                                    · rcases p6273_3 (m.d 3 4) (by simp) with h6314 | h6314
                                      · rcases p6273_3 (m.d 3 5) (by simp) with h6315 | h6315
                                        · rcases h5bigk with h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c | h6316c
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [hlam, p6316_0]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h6193, h6194, h6199, h7, hc23, hc34, hlam, hphi, p6316_1]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h6193, h6204, h7, hc23, hc34, hlam, hphi, p6316_1]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h5823, hlam, p6316_1]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            rcases p6316_3 (m.d 0 5) (by simp) with h6321 | h6321
                                            · rcases p6316_3 (m.d 1 5) (by simp) with h6322 | h6322
                                              · linarith only [h3, h6322, hlam]
                                              · linarith only [h6201, h6322, hlam]
                                            · linarith only [h6193, h6321, hlam]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h3, hlam, p6316_0]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [hlam, p6316_0]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h3, h6204, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6316_1]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h6199, hlam, p6316_1]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h0, h6195, hc01, hc45, hlam, hphi, ht0b, ht5b, p6208_1, p6316_1]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h6, hlam, p6316_1]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h6196, hlam, p6316_1]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [hlam, p6316_0]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h6204, hlam, p6316_1]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h0, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p6316_1]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h1, h5823, h6194, hc23, hc35, hlam, hphi, p6316_1]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h6194, h6199, hc23, hc35, hlam, hphi, p6316_1]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h6204, hc23, hc35, hlam, hphi, p6316_1]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [hlam, p6316_0]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            rcases p6316_3 (m.d 0 5) (by simp) with h6340 | h6340
                                            · linarith only [h5823, h6340, hlam]
                                            · linarith only [h6193, h6340, hlam]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h6193, hlam, p6316_0]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h6201, hlam, p6316_0]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h6206, hlam, p6316_0]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [h6207, hlam, p6316_0]
                                          · have p6316_0 := h6316c.1
                                            have p6316_1 := h6316c.2.1
                                            have p6316_2 := h6316c.2.2.1
                                            have p6316_3 := h6316c.2.2.2
                                            linarith only [hlam, p6316_0]
                                        · linarith only [h6315, hlam, p6273_0]
                                      · linarith only [h6314, h7, hlam]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                rcases p6273_3 (m.d 0 3) (by simp) with h6350 | h6350
                                · linarith only [h5823, h6350, hlam]
                                · linarith only [h1, h6350, hlam]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                rcases p6273_3 (m.d 0 3) (by simp) with h6353 | h6353
                                · linarith only [h5823, h6353, hlam]
                                · linarith only [h4, h6353, hlam]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [h6207, hlam, p6273_0]
                              · have p6273_0 := h6273c.1
                                have p6273_1 := h6273c.2.1
                                have p6273_2 := h6273c.2.2.1
                                have p6273_3 := h6273c.2.2.2
                                linarith only [hlam, p6273_0]
                          · linarith only [h6201, h6270, hlam]
                      · linarith only [h6196, h6267, hlam]
                    · linarith only [h3, h6266, hlam]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [h3, hlam, p6208_0]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [h6196, hlam, p6208_1]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    rcases p6208_3 (m.d 0 1) (by simp) with h6363 | h6363
                    · rcases p6208_3 (m.d 1 2) (by simp) with h6364 | h6364
                      · rcases p6208_3 (m.d 1 3) (by simp) with h6365 | h6365
                        · linarith only [h6199, h6365, hlam]
                        · rcases p6208_3 (m.d 1 4) (by simp) with h6367 | h6367
                          · rcases p6208_3 (m.d 1 5) (by simp) with h6368 | h6368
                            · rcases h3bigk with h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c | h6369c
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [h6194, h7, hc23, hc34, hlam, hphi, p6369_1]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [h7, hc23, hc34, hlam, hphi, p6369_1]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [h7, hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [h5823, hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [h1, hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [h3, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6208_1, p6369_1]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [h6197, hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [h6199, hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [h4, hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [h6194, hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [h6202, hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [h6204, hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                rcases p6369_3 (m.d 0 3) (by simp) with h6385 | h6385
                                · linarith only [h6385, hlam, p6369_0]
                                · rcases p6369_3 (m.d 1 3) (by simp) with h6387 | h6387
                                  · linarith only [h6197, h6387, hlam]
                                  · rcases p6369_3 (m.d 2 3) (by simp) with h6389 | h6389
                                    · linarith only [h6202, h6389, hlam]
                                    · rcases p6369_3 (m.d 3 4) (by simp) with h6391 | h6391
                                      · rcases p6369_3 (m.d 3 5) (by simp) with h6392 | h6392
                                        · linarith only [h6207, h6392, hlam]
                                        · linarith only [h5823, h6392, hlam]
                                      · linarith only [h6391, hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                rcases p6369_3 (m.d 0 3) (by simp) with h6396 | h6396
                                · linarith only [h6396, h7, hlam]
                                · linarith only [h1, h6396, hlam]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                rcases p6369_3 (m.d 0 3) (by simp) with h6399 | h6399
                                · linarith only [h6399, h7, hlam]
                                · linarith only [h4, h6399, hlam]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [h3, h5823, hc13, hc34, hlam, hphi, p6208_1, p6369_1]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                rcases p6369_3 (m.d 0 3) (by simp) with h6404 | h6404
                                · linarith only [h6404, hlam, p6369_0]
                                · rcases p6369_3 (m.d 1 3) (by simp) with h6406 | h6406
                                  · linarith only [h6199, h6406, hlam]
                                  · rcases p6369_3 (m.d 2 3) (by simp) with h6408 | h6408
                                    · linarith only [h6204, h6408, hlam]
                                    · rcases p6369_3 (m.d 3 4) (by simp) with h6410 | h6410
                                      · rcases p6369_3 (m.d 3 5) (by simp) with h6411 | h6411
                                        · rcases h5bigk with h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c | h6412c
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [hlam, p6412_0]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h6194, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6208_1, p6412_1]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h5823, h6204, h6207, hc23, hc34, hlam, hphi, p6412_1]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h5823, hlam, p6412_1]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            rcases p6412_3 (m.d 0 5) (by simp) with h6417 | h6417
                                            · rcases p6412_3 (m.d 1 5) (by simp) with h6418 | h6418
                                              · linarith only [h3, h6418, hlam]
                                              · linarith only [h6201, h6418, hlam]
                                            · linarith only [h6193, h6417, hlam]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h3, hlam, p6412_0]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [hlam, p6412_0]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h3, h6204, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6412_1]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h6199, hlam, p6412_1]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h0, h6195, h6201, hc01, hc45, hlam, hphi, ht0b, ht5b, p6412_1]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h6, hlam, p6412_1]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h6196, hlam, p6412_1]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [hlam, p6412_0]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h6204, hlam, p6412_1]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h0, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p6412_1]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h5823, h6207, hc03, hc34, hlam, hphi, p6412_1]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h6194, h6207, hc23, hc34, hlam, hphi, p6208_1, p6412_1]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h6204, h6207, hc23, hc34, hlam, hphi, p6412_1]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [hlam, p6412_0]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            rcases p6412_3 (m.d 0 5) (by simp) with h6436 | h6436
                                            · linarith only [h5823, h6436, hlam]
                                            · linarith only [h6193, h6436, hlam]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h6193, hlam, p6412_0]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h6201, hlam, p6412_0]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h6206, hlam, p6412_0]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [h6207, hlam, p6412_0]
                                          · have p6412_0 := h6412c.1
                                            have p6412_1 := h6412c.2.1
                                            have p6412_2 := h6412c.2.2.1
                                            have p6412_3 := h6412c.2.2.2
                                            linarith only [hlam, p6412_0]
                                        · linarith only [h6411, hlam, p6369_0]
                                      · linarith only [h6410, h7, hlam]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                rcases p6369_3 (m.d 0 3) (by simp) with h6446 | h6446
                                · linarith only [h5823, h6446, hlam]
                                · linarith only [h1, h6446, hlam]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                rcases p6369_3 (m.d 0 3) (by simp) with h6449 | h6449
                                · linarith only [h5823, h6449, hlam]
                                · linarith only [h4, h6449, hlam]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [h6207, hlam, p6369_0]
                              · have p6369_0 := h6369c.1
                                have p6369_1 := h6369c.2.1
                                have p6369_2 := h6369c.2.2.1
                                have p6369_3 := h6369c.2.2.2
                                linarith only [hlam, p6369_0]
                            · linarith only [h6199, h6368, hlam]
                          · linarith only [h6197, h6367, hlam]
                      · linarith only [h6194, h6364, hlam]
                    · linarith only [h1, h6363, hlam]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [h6201, hlam, p6208_0]
                  · have p6208_0 := h6208c.1
                    have p6208_1 := h6208c.2.1
                    have p6208_2 := h6208c.2.2.1
                    have p6208_3 := h6208c.2.2.2
                    linarith only [hlam, p6208_0]
                · linarith only [h5, h6206, h6207, h7, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h6461 | h6461
                · rcases h1bigk with h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [hlam, p6462_0]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h6195, h6201, h6202, h6206, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6462_1]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    rcases p6462_3 (m.d 0 1) (by simp) with h6465 | h6465
                    · rcases p6462_3 (m.d 1 2) (by simp) with h6466 | h6466
                      · linarith only [h0, h6466, hlam]
                      · linarith only [h6194, h6466, hlam]
                    · linarith only [h6465, hlam, p6462_0]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h6201, h6202, h6206, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6462_1]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    rcases p6462_3 (m.d 0 1) (by simp) with h6471 | h6471
                    · rcases p6462_3 (m.d 1 2) (by simp) with h6472 | h6472
                      · linarith only [h0, h6472, hlam]
                      · linarith only [h6196, h6472, hlam]
                    · linarith only [h6471, hlam, p6462_0]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h0, hlam, p6462_0]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [hlam, p6462_0]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    rcases p6462_3 (m.d 0 1) (by simp) with h6478 | h6478
                    · rcases p6462_3 (m.d 1 2) (by simp) with h6479 | h6479
                      · rcases p6462_3 (m.d 1 3) (by simp) with h6480 | h6480
                        · linarith only [h6194, h6480, hlam]
                        · rcases p6462_3 (m.d 1 4) (by simp) with h6482 | h6482
                          · linarith only [h6195, h6482, hlam]
                          · linarith only [h6197, h6482, hlam]
                      · linarith only [h6194, h6479, hlam]
                    · linarith only [h1, h6478, hlam]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h0, h6201, h6202, h6206, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6462_1]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h0, h6201, h6202, h6206, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6462_1]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h1, hlam, p6462_0]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h6194, hlam, p6462_1]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [hlam, p6462_0]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h6197, hlam, p6462_1]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h6199, hlam, p6462_1]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h2, hlam, p6462_0]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h6195, hlam, p6462_1]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    rcases p6462_3 (m.d 0 1) (by simp) with h6496 | h6496
                    · rcases p6462_3 (m.d 1 2) (by simp) with h6497 | h6497
                      · rcases p6462_3 (m.d 1 3) (by simp) with h6498 | h6498
                        · linarith only [h6197, h6498, hlam]
                        · rcases p6462_3 (m.d 1 4) (by simp) with h6500 | h6500
                          · rcases p6462_3 (m.d 1 5) (by simp) with h6501 | h6501
                            · linarith only [h6201, h6501, hlam]
                            · linarith only [h6199, h6501, hlam]
                          · linarith only [h6197, h6500, hlam]
                      · linarith only [h6194, h6497, hlam]
                    · linarith only [h1, h6496, hlam]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [hlam, p6462_0]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h0, h6195, h6201, h6202, h6206, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6462_1]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h3, hlam, p6462_0]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h6196, hlam, p6462_1]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    rcases p6462_3 (m.d 0 1) (by simp) with h6511 | h6511
                    · rcases p6462_3 (m.d 1 2) (by simp) with h6512 | h6512
                      · rcases p6462_3 (m.d 1 3) (by simp) with h6513 | h6513
                        · linarith only [h6199, h6513, hlam]
                        · rcases p6462_3 (m.d 1 4) (by simp) with h6515 | h6515
                          · rcases p6462_3 (m.d 1 5) (by simp) with h6516 | h6516
                            · rcases h3bigk with h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [h7, hc13, hc34, hlam, hphi, p6517_1]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [h7, hc23, hc34, hlam, hphi, p6517_1]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [h7, hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [h5823, hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [h1, hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [h1, h5823, h6461, hc23, hc34, hlam, hphi, p6517_1]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [h6197, hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [h6199, hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [h4, hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [h6194, hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [h6202, hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [h6204, hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                rcases p6517_3 (m.d 0 3) (by simp) with h6533 | h6533
                                · linarith only [h6533, hlam, p6517_0]
                                · rcases p6517_3 (m.d 1 3) (by simp) with h6535 | h6535
                                  · linarith only [h6197, h6535, hlam]
                                  · rcases p6517_3 (m.d 2 3) (by simp) with h6537 | h6537
                                    · linarith only [h6202, h6537, hlam]
                                    · rcases p6517_3 (m.d 3 4) (by simp) with h6539 | h6539
                                      · rcases p6517_3 (m.d 3 5) (by simp) with h6540 | h6540
                                        · linarith only [h6461, h6540, hlam]
                                        · linarith only [h5823, h6540, hlam]
                                      · linarith only [h6539, hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                rcases p6517_3 (m.d 0 3) (by simp) with h6544 | h6544
                                · linarith only [h6544, h7, hlam]
                                · linarith only [h1, h6544, hlam]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                rcases p6517_3 (m.d 0 3) (by simp) with h6547 | h6547
                                · linarith only [h6547, h7, hlam]
                                · linarith only [h4, h6547, hlam]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [h5823, hc03, hc34, hlam, hphi, p6517_1]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                rcases p6517_3 (m.d 0 3) (by simp) with h6552 | h6552
                                · linarith only [h6552, hlam, p6517_0]
                                · rcases p6517_3 (m.d 1 3) (by simp) with h6554 | h6554
                                  · linarith only [h6199, h6554, hlam]
                                  · rcases p6517_3 (m.d 2 3) (by simp) with h6556 | h6556
                                    · linarith only [h6204, h6556, hlam]
                                    · rcases p6517_3 (m.d 3 4) (by simp) with h6558 | h6558
                                      · rcases p6517_3 (m.d 3 5) (by simp) with h6559 | h6559
                                        · rcases h5bigk with h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [hlam, p6560_0]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6193, h6196, h6202, h6206, h7, hc23, hc34, hlam, hphi, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6193, h6202, h6206, h7, hc23, hc34, hlam, hphi, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h5823, hlam, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6193, h6202, h6206, h7, hc23, hc34, hlam, hphi, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h3, hlam, p6560_0]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [hlam, p6560_0]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h3, h6202, h6206, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6199, hlam, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h0, h6195, h6201, h6202, h6206, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6, hlam, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6196, hlam, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [hlam, p6560_0]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6204, hlam, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6206, hlam, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6, h6202, h6206, hc23, hc35, hlam, hphi, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6196, h6202, h6206, hc23, hc35, hlam, hphi, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6202, h6206, hc23, hc35, hlam, hphi, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [hlam, p6560_0]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6202, h6206, h6461, hc23, hc34, hlam, hphi, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6193, hlam, p6560_0]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6201, hlam, p6560_0]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6202, h6206, hc23, hc45, hlam, hphi, ht34, p6560_1]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [h6461, hlam, p6560_0]
                                          · have p6560_0 := h6560c.1
                                            have p6560_1 := h6560c.2.1
                                            have p6560_2 := h6560c.2.2.1
                                            have p6560_3 := h6560c.2.2.2
                                            linarith only [hlam, p6560_0]
                                        · linarith only [h6559, hlam, p6517_0]
                                      · linarith only [h6558, h7, hlam]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                rcases p6517_3 (m.d 0 3) (by simp) with h6588 | h6588
                                · linarith only [h5823, h6588, hlam]
                                · linarith only [h1, h6588, hlam]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                rcases p6517_3 (m.d 0 3) (by simp) with h6591 | h6591
                                · linarith only [h5823, h6591, hlam]
                                · linarith only [h4, h6591, hlam]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [h6461, hlam, p6517_0]
                              · have p6517_0 := h6517c.1
                                have p6517_1 := h6517c.2.1
                                have p6517_2 := h6517c.2.2.1
                                have p6517_3 := h6517c.2.2.2
                                linarith only [hlam, p6517_0]
                            · linarith only [h6199, h6516, hlam]
                          · linarith only [h6197, h6515, hlam]
                      · linarith only [h6194, h6512, hlam]
                    · linarith only [h1, h6511, hlam]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [h6201, hlam, p6462_0]
                  · have p6462_0 := h6462c.1
                    have p6462_1 := h6462c.2.1
                    have p6462_2 := h6462c.2.2.1
                    have p6462_3 := h6462c.2.2.2
                    linarith only [hlam, p6462_0]
                · linarith only [h2, h6201, h6461, h7, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h6603 | h6603
          · linarith only [h1, h6193, h6194, h6201, h6603, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h6605 | h6605
            · linarith only [h5823, h6193, h6194, h6197, h6201, h6605, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6607 | h6607
              · linarith only [h0, h6195, h6197, h6201, h6607, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h6609 | h6609
                · rcases h1bigk with h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c | h6610c
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [hlam, p6610_0]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    rcases p6610_3 (m.d 0 1) (by simp) with h6612 | h6612
                    · rcases p6610_3 (m.d 1 2) (by simp) with h6613 | h6613
                      · linarith only [h6613, hlam, p6610_0]
                      · rcases p6610_3 (m.d 1 3) (by simp) with h6615 | h6615
                        · linarith only [h1, h6615, hlam]
                        · rcases p6610_3 (m.d 1 4) (by simp) with h6617 | h6617
                          · linarith only [h2, h6617, hlam]
                          · rcases p6610_3 (m.d 1 5) (by simp) with h6619 | h6619
                            · linarith only [h3, h6619, hlam]
                            · rcases h3bigk with h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c | h6621c
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [h6194, h7, hc23, hc34, hlam, hphi, p6621_1]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [h7, hc23, hc34, hlam, hphi, p6621_1]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [h7, hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [h5823, hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [h1, hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [h5, h6193, h6197, h6201, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6621_1]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [h6197, hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [h6199, hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [h4, hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [h6194, hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [h6603, hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [h6605, hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                rcases p6621_3 (m.d 0 3) (by simp) with h6637 | h6637
                                · linarith only [h6637, hlam, p6621_0]
                                · rcases p6621_3 (m.d 1 3) (by simp) with h6639 | h6639
                                  · linarith only [h6197, h6639, hlam]
                                  · rcases p6621_3 (m.d 2 3) (by simp) with h6641 | h6641
                                    · linarith only [h6603, h6641, hlam]
                                    · rcases p6621_3 (m.d 3 4) (by simp) with h6643 | h6643
                                      · rcases p6621_3 (m.d 3 5) (by simp) with h6644 | h6644
                                        · linarith only [h6609, h6644, hlam]
                                        · linarith only [h5823, h6644, hlam]
                                      · linarith only [h6643, hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                rcases p6621_3 (m.d 0 3) (by simp) with h6648 | h6648
                                · linarith only [h6648, h7, hlam]
                                · linarith only [h1, h6648, hlam]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                rcases p6621_3 (m.d 0 3) (by simp) with h6651 | h6651
                                · linarith only [h6651, h7, hlam]
                                · linarith only [h4, h6651, hlam]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [h5823, h6193, h6197, h6201, hc13, hc34, hlam, hphi, p6621_1]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                rcases p6621_3 (m.d 0 3) (by simp) with h6656 | h6656
                                · linarith only [h6656, hlam, p6621_0]
                                · rcases p6621_3 (m.d 1 3) (by simp) with h6658 | h6658
                                  · linarith only [h6199, h6658, hlam]
                                  · rcases p6621_3 (m.d 2 3) (by simp) with h6660 | h6660
                                    · linarith only [h6605, h6660, hlam]
                                    · rcases p6621_3 (m.d 3 4) (by simp) with h6662 | h6662
                                      · rcases p6621_3 (m.d 3 5) (by simp) with h6663 | h6663
                                        · rcases h5bigk with h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c | h6664c
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [hlam, p6664_0]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6193, h6194, h6199, h7, hc23, hc34, hlam, hphi, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6193, h6603, h6607, h7, hc23, hc34, hlam, hphi, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h5823, hlam, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6193, h6194, h6197, h6201, h7, hc23, hc34, hlam, hphi, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h3, hlam, p6664_0]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [hlam, p6664_0]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h3, h6607, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6199, hlam, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6201, hlam, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6, hlam, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6196, hlam, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [hlam, p6664_0]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6605, hlam, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6607, hlam, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h1, h5823, h6194, hc23, hc35, hlam, hphi, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6194, h6199, hc23, hc35, hlam, hphi, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6603, h6607, hc23, hc35, hlam, hphi, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [hlam, p6664_0]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6194, h6197, h6201, h6609, hc23, hc34, hlam, hphi, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6193, hlam, p6664_0]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6193, h6194, h6197, h6201, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6193, h6603, h6607, h7, hc23, hc34, hlam, hphi, p6664_1]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [h6609, hlam, p6664_0]
                                          · have p6664_0 := h6664c.1
                                            have p6664_1 := h6664c.2.1
                                            have p6664_2 := h6664c.2.2.1
                                            have p6664_3 := h6664c.2.2.2
                                            linarith only [hlam, p6664_0]
                                        · linarith only [h6663, hlam, p6621_0]
                                      · linarith only [h6662, h7, hlam]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                rcases p6621_3 (m.d 0 3) (by simp) with h6692 | h6692
                                · linarith only [h5823, h6692, hlam]
                                · linarith only [h1, h6692, hlam]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                rcases p6621_3 (m.d 0 3) (by simp) with h6695 | h6695
                                · linarith only [h5823, h6695, hlam]
                                · linarith only [h4, h6695, hlam]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [h6609, hlam, p6621_0]
                              · have p6621_0 := h6621c.1
                                have p6621_1 := h6621c.2.1
                                have p6621_2 := h6621c.2.2.1
                                have p6621_3 := h6621c.2.2.2
                                linarith only [hlam, p6621_0]
                    · linarith only [h6612, hlam, p6610_0]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    rcases p6610_3 (m.d 0 1) (by simp) with h6701 | h6701
                    · rcases p6610_3 (m.d 1 2) (by simp) with h6702 | h6702
                      · linarith only [h0, h6702, hlam]
                      · linarith only [h6194, h6702, hlam]
                    · linarith only [h6701, hlam, p6610_0]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    rcases p6610_3 (m.d 0 1) (by simp) with h6706 | h6706
                    · rcases p6610_3 (m.d 1 2) (by simp) with h6707 | h6707
                      · linarith only [h0, h6707, hlam]
                      · linarith only [h6195, h6707, hlam]
                    · linarith only [h6706, hlam, p6610_0]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    rcases p6610_3 (m.d 0 1) (by simp) with h6711 | h6711
                    · rcases p6610_3 (m.d 1 2) (by simp) with h6712 | h6712
                      · linarith only [h0, h6712, hlam]
                      · linarith only [h6196, h6712, hlam]
                    · linarith only [h6711, hlam, p6610_0]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [h0, hlam, p6610_0]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [hlam, p6610_0]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    rcases p6610_3 (m.d 0 1) (by simp) with h6718 | h6718
                    · rcases p6610_3 (m.d 1 2) (by simp) with h6719 | h6719
                      · rcases p6610_3 (m.d 1 3) (by simp) with h6720 | h6720
                        · linarith only [h6194, h6720, hlam]
                        · rcases p6610_3 (m.d 1 4) (by simp) with h6722 | h6722
                          · linarith only [h6195, h6722, hlam]
                          · linarith only [h6197, h6722, hlam]
                      · linarith only [h6194, h6719, hlam]
                    · linarith only [h1, h6718, hlam]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    rcases p6610_3 (m.d 0 1) (by simp) with h6727 | h6727
                    · rcases p6610_3 (m.d 1 2) (by simp) with h6728 | h6728
                      · rcases p6610_3 (m.d 1 3) (by simp) with h6729 | h6729
                        · linarith only [h6194, h6729, hlam]
                        · rcases p6610_3 (m.d 1 4) (by simp) with h6731 | h6731
                          · linarith only [h6195, h6731, hlam]
                          · rcases p6610_3 (m.d 1 5) (by simp) with h6733 | h6733
                            · linarith only [h6196, h6733, hlam]
                            · linarith only [h6201, h6733, hlam]
                      · linarith only [h6195, h6728, hlam]
                    · linarith only [h2, h6727, hlam]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    rcases p6610_3 (m.d 0 1) (by simp) with h6738 | h6738
                    · rcases p6610_3 (m.d 1 2) (by simp) with h6739 | h6739
                      · rcases p6610_3 (m.d 1 3) (by simp) with h6740 | h6740
                        · linarith only [h6194, h6740, hlam]
                        · rcases p6610_3 (m.d 1 4) (by simp) with h6742 | h6742
                          · linarith only [h6195, h6742, hlam]
                          · rcases p6610_3 (m.d 1 5) (by simp) with h6744 | h6744
                            · linarith only [h6196, h6744, hlam]
                            · rcases h3bigk with h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c | h6746c
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [h6194, h7, hc23, hc34, hlam, hphi, p6746_1]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [h7, hc23, hc34, hlam, hphi, p6746_1]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [h7, hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [h5823, hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [h1, hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [h0, h6197, h6201, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6610_1, p6746_1]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [h6197, hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [h6199, hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [h4, hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [h6194, hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [h6603, hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [h6605, hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                rcases p6746_3 (m.d 0 3) (by simp) with h6762 | h6762
                                · linarith only [h6762, hlam, p6746_0]
                                · rcases p6746_3 (m.d 1 3) (by simp) with h6764 | h6764
                                  · linarith only [h6197, h6764, hlam]
                                  · rcases p6746_3 (m.d 2 3) (by simp) with h6766 | h6766
                                    · linarith only [h6603, h6766, hlam]
                                    · rcases p6746_3 (m.d 3 4) (by simp) with h6768 | h6768
                                      · rcases p6746_3 (m.d 3 5) (by simp) with h6769 | h6769
                                        · linarith only [h6609, h6769, hlam]
                                        · linarith only [h5823, h6769, hlam]
                                      · linarith only [h6768, hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                rcases p6746_3 (m.d 0 3) (by simp) with h6773 | h6773
                                · linarith only [h6773, h7, hlam]
                                · linarith only [h1, h6773, hlam]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                rcases p6746_3 (m.d 0 3) (by simp) with h6776 | h6776
                                · linarith only [h6776, h7, hlam]
                                · linarith only [h4, h6776, hlam]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [h5823, hc03, hc34, hlam, hphi, p6746_1]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                rcases p6746_3 (m.d 0 3) (by simp) with h6781 | h6781
                                · linarith only [h6781, hlam, p6746_0]
                                · rcases p6746_3 (m.d 1 3) (by simp) with h6783 | h6783
                                  · linarith only [h6199, h6783, hlam]
                                  · rcases p6746_3 (m.d 2 3) (by simp) with h6785 | h6785
                                    · linarith only [h6605, h6785, hlam]
                                    · rcases p6746_3 (m.d 3 4) (by simp) with h6787 | h6787
                                      · rcases p6746_3 (m.d 3 5) (by simp) with h6788 | h6788
                                        · rcases h5bigk with h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c | h6789c
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [hlam, p6789_0]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6193, h6195, h6201, h6603, h7, hc23, hc34, hlam, hphi, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6193, h6603, h6607, h7, hc23, hc34, hlam, hphi, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h5823, hlam, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6193, h6195, h6201, h6603, h7, hc23, hc34, hlam, hphi, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h3, hlam, p6789_0]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [hlam, p6789_0]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h3, h6603, h6607, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6199, hlam, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6201, hlam, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6, hlam, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6196, hlam, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [hlam, p6789_0]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6605, hlam, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6607, hlam, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6, h6603, h6607, hc23, hc35, hlam, hphi, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6196, h6603, h6607, hc23, hc35, hlam, hphi, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6603, h6607, hc23, hc35, hlam, hphi, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [hlam, p6789_0]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6195, h6201, h6603, h6609, hc23, hc34, hlam, hphi, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6193, hlam, p6789_0]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6196, h6603, h6607, hc23, hc45, hlam, hphi, ht34, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6193, h6603, h6607, h7, hc23, hc34, hlam, hphi, p6789_1]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [h6609, hlam, p6789_0]
                                          · have p6789_0 := h6789c.1
                                            have p6789_1 := h6789c.2.1
                                            have p6789_2 := h6789c.2.2.1
                                            have p6789_3 := h6789c.2.2.2
                                            linarith only [hlam, p6789_0]
                                        · linarith only [h6788, hlam, p6746_0]
                                      · linarith only [h6787, h7, hlam]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                rcases p6746_3 (m.d 0 3) (by simp) with h6817 | h6817
                                · linarith only [h5823, h6817, hlam]
                                · linarith only [h1, h6817, hlam]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                rcases p6746_3 (m.d 0 3) (by simp) with h6820 | h6820
                                · linarith only [h5823, h6820, hlam]
                                · linarith only [h4, h6820, hlam]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [h6609, hlam, p6746_0]
                              · have p6746_0 := h6746c.1
                                have p6746_1 := h6746c.2.1
                                have p6746_2 := h6746c.2.2.1
                                have p6746_3 := h6746c.2.2.2
                                linarith only [hlam, p6746_0]
                      · linarith only [h6196, h6739, hlam]
                    · linarith only [h3, h6738, hlam]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [h1, hlam, p6610_0]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [h6194, hlam, p6610_1]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [hlam, p6610_0]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [h6197, hlam, p6610_1]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [h6199, hlam, p6610_1]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [h2, hlam, p6610_0]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [h6195, hlam, p6610_1]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [h6193, h6194, h6201, h7, hc23, hc34, hlam, hphi, p6610_1]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [hlam, p6610_0]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [h6201, hlam, p6610_1]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [h3, hlam, p6610_0]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [h6196, hlam, p6610_1]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [h6193, h6194, h6201, h7, hc23, hc34, hlam, hphi, p6610_1]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [h6193, h6195, h6201, h6603, h7, hc23, hc34, hlam, hphi, p6610_1]
                  · have p6610_0 := h6610c.1
                    have p6610_1 := h6610c.2.1
                    have p6610_2 := h6610c.2.2.1
                    have p6610_3 := h6610c.2.2.2
                    linarith only [hlam, p6610_0]
                · linarith only [h6193, h6609, h7, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h6843 | h6843
    · linarith only [h1, h6843, h7, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h6845 | h6845
      · linarith only [h1, h5823, h6, h6196, h6845, h7, hc12, hc34, hlam, hphi, ht23]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h6847 | h6847
        · linarith only [h6195, h6196, h6847, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h6849 | h6849
          · linarith only [h0, h6, h6194, h6196, h6849, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h6851 | h6851
            · linarith only [h1, h5823, h6, h6194, h6196, h6851, h7, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6853 | h6853
              · linarith only [h0, h6, h6195, h6196, h6843, h6847, h6853, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h6193, h6194, h6196, h6853, h7, hc23, hc34, hlam, hphi]

end R2N4
